#!/usr/bin/env node
/*
 * aptcheck.cjs — one-shot NYC apartment vetting tool.
 *
 * Usage:  node aptcheck.cjs "<streeteasy-or-apartments.com-URL>"
 *         node aptcheck.cjs --addr "439 54th St, Brooklyn, NY 11220"   (skip scrape)
 *
 * Does three things:
 *   1. Scrapes the listing via headed Playwright + stealth (bypasses CoStar/Akamai + StreetEasy WAF)
 *   2. Runs NYC HPD open-violation lookup on the address
 *   3. Runs Google Routes API transit commute to 1 Manhattan West (Mon 8:30am)
 * Then prints a clean report + heuristic verdict.
 *
 * Requires: Playwright (node), GOOGLE_ROUTES_API_KEY in ../.env
 */
const fs = require('fs');
const path = require('path');
const { chromium } = require('/opt/homebrew/lib/node_modules/playwright');

const DEST = '1 Manhattan West, 395 9th Ave, New York, NY 10001';
const DEPART = '2026-06-02T12:30:00Z'; // Mon 8:30am EDT benchmark

function loadKey() {
  try {
    const env = fs.readFileSync(path.join(__dirname, '..', '.env'), 'utf8');
    const m = env.match(/GOOGLE_ROUTES_API_KEY=(.+)/);
    return m ? m[1].trim() : null;
  } catch { return null; }
}

// ---- address parsing ----
const SUFFIX = { st:'STREET', street:'STREET', ave:'AVENUE', avenue:'AVENUE', blvd:'BOULEVARD', boulevard:'BOULEVARD',
  rd:'ROAD', road:'ROAD', dr:'DRIVE', drive:'DRIVE', pl:'PLACE', place:'PLACE', ln:'LANE', lane:'LANE', ct:'COURT',
  ter:'TERRACE', terrace:'TERRACE', pkwy:'PARKWAY', parkway:'PARKWAY' };
const BORO = { manhattan:'MANHATTAN', 'new york':'MANHATTAN', bronx:'BRONX', brooklyn:'BROOKLYN', kings:'BROOKLYN',
  queens:'QUEENS', 'staten island':'STATEN ISLAND' };

function parseAddress(text) {
  // e.g. "439 54th St, Brooklyn, NY 11220"  or  "32-15 93rd Street, East Elmhurst, NY 11369"
  const m = text.match(/(\d+(?:-\d+)?)\s+([\w]+?)(?:st|nd|rd|th)?\s+(St|Street|Ave|Avenue|Blvd|Boulevard|Rd|Road|Dr|Drive|Pl|Place|Ln|Lane|Ct|Ter|Terrace|Pkwy|Parkway)\b[,\s]+([\w\s]+?),?\s+NY\s+(\d{5})/i);
  if (!m) return null;
  let [, hn, streetCore, suf, locality, zip] = m;
  // streetCore may include a leading ordinal word part; strip trailing ordinal letters already handled by regex (?:st|nd|rd|th)?
  streetCore = streetCore.replace(/(st|nd|rd|th)$/i, '');
  const streetname = (streetCore + ' ' + (SUFFIX[suf.toLowerCase()] || suf.toUpperCase())).toUpperCase().replace(/\s+/g, ' ').trim();
  // borough from locality / known neighborhoods
  let boro = null;
  const loc = locality.toLowerCase();
  for (const k of Object.keys(BORO)) if (loc.includes(k)) { boro = BORO[k]; break; }
  // neighborhood → borough fallbacks
  if (!boro) {
    if (/astoria|elmhurst|jackson heights|woodside|sunnyside|forest hills|rego park|flushing|corona|maspeth|ridgewood|long island city|jamaica/.test(loc)) boro = 'QUEENS';
    else if (/sunset park|williamsburg|bushwick|park slope|bay ridge|greenpoint|bed.?stuy/.test(loc)) boro = 'BROOKLYN';
    else if (/harlem|inwood|washington heights|morningside|chelsea|midtown|upper/.test(loc)) boro = 'MANHATTAN';
  }
  const full = `${hn} ${streetCore.trim()} ${suf}, ${locality.trim()}, NY ${zip}`;
  return { hn, streetname, boro, zip, locality: locality.trim(), full };
}

// ---- HPD lookup ----
async function hpd(addr) {
  let where = `housenumber='${addr.hn}' AND streetname='${addr.streetname}'`;
  if (addr.boro) where += ` AND boro='${addr.boro}'`;
  const url = `https://data.cityofnewyork.us/resource/wvxf-dwi5.json?$where=${encodeURIComponent(where)}&$limit=600`;
  const r = await fetch(url);
  const vs = await r.json();
  if (!Array.isArray(vs)) return { error: 'hpd query failed' };
  const open = vs.filter(v => !(v.currentstatus || '').includes('NOV CLOSED'));
  const cls = c => open.filter(v => v.class === c).length;
  const recent = open.filter(v => (v.inspectiondate || '').slice(0,4) >= '2023');
  const recentSerious = recent.filter(v => v.class === 'C' || v.class === 'B')
    .sort((a,b) => (b.inspectiondate||'').localeCompare(a.inspectiondate||''))
    .slice(0,4)
    .map(v => `[${v.class}] ${(v.inspectiondate||'').slice(0,10)}: ${(v.novdescription||'').slice(0,90)}`);
  return { total: open.length, C: cls('C'), B: cls('B'), A: cls('A'), I: cls('I'), recent: recent.length, recentSerious };
}

// ---- commute ----
async function commute(fullAddr, key) {
  if (!key) return { error: 'no API key' };
  const r = await fetch('https://routes.googleapis.com/directions/v2:computeRoutes', {
    method: 'POST',
    headers: { 'Content-Type':'application/json', 'X-Goog-Api-Key': key,
      'X-Goog-FieldMask':'routes.duration,routes.legs.steps.transitDetails,routes.legs.steps.travelMode' },
    body: JSON.stringify({ origin:{address:fullAddr}, destination:{address:DEST}, travelMode:'TRANSIT', departureTime:DEPART })
  });
  const d = await r.json();
  if (!d.routes || !d.routes[0]) return { error: JSON.stringify(d).slice(0,200) };
  const route = d.routes[0];
  const mins = Math.round(parseInt(route.duration) / 60);
  const legs = [];
  for (const leg of route.legs || [])
    for (const s of leg.steps || [])
      if (s.travelMode === 'TRANSIT') {
        const t = s.transitDetails || {};
        const line = (t.transitLine||{}).nameShort || (t.transitLine||{}).name || '?';
        legs.push(`${line}: ${((t.stopDetails||{}).departureStop||{}).name} -> ${((t.stopDetails||{}).arrivalStop||{}).name}`);
      }
  return { mins, legs };
}

// ---- scrape ----
async function scrape(url) {
  const b = await chromium.launch({ headless: false, args:['--disable-blink-features=AutomationControlled'] });
  const ctx = await b.newContext({
    userAgent:'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36',
    viewport:{width:1440,height:900}, locale:'en-US', timezoneId:'America/New_York'
  });
  await ctx.addInitScript(() => {
    Object.defineProperty(navigator,'webdriver',{get:()=>undefined});
    Object.defineProperty(navigator,'plugins',{get:()=>[1,2,3,4,5]});
    Object.defineProperty(navigator,'languages',{get:()=>['en-US','en']});
    window.chrome={runtime:{}};
  });
  const p = await ctx.newPage();
  let txt = '';
  try {
    await p.goto(url, { waitUntil:'domcontentloaded', timeout:35000 });
    await p.waitForTimeout(4500);
    txt = await p.evaluate(() => document.body.innerText);
  } catch(e) { txt = 'SCRAPE_ERR ' + e.message; }
  await b.close();
  return txt;
}

function extract(txt) {
  const price = (txt.match(/\$[\d,]{3,6}\s*(?:\/\s*month|\/mo)?/i)||[])[0] || '?';
  const beds = (txt.match(/\b(Studio|[1-4]\s*Bed(?:room)?s?)\b/i)||[])[0] || '?';
  const sqft = (txt.match(/([\d,]+)\s*(?:sq\.?\s*ft|sqft|square feet)/i)||[])[0] || '?';
  const flags = [];
  const has = re => re.test(txt);
  if (has(/rent[\s-]?stabiliz/i)) flags.push('RENT STABILIZED');
  if (has(/co-?op/i)) flags.push('⚠️ CO-OP (likely board approval)');
  if (has(/board approval/i)) flags.push('⚠️ BOARD APPROVAL mentioned');
  if (has(/no broker fee|rent by owner|by owner/i)) flags.push('no broker fee / owner-direct');
  if (has(/guarantor/i)) flags.push('guarantor mentioned');
  if (has(/utilities included|heat.{0,15}(water|hot water).{0,15}included|all utilities/i)) flags.push('utilities included');
  if (has(/in-?unit (washer|laundry)|washer.{0,5}dryer/i)) flags.push('in-unit W/D');
  if (has(/laundry in building|laundry room/i)) flags.push('laundry in building');
  if (has(/no fee|fare act/i)) flags.push('no fee (FARE)');
  if (has(/furnished/i)) flags.push('furnished?');
  if (has(/shared (apartment|kitchen|bathroom)|by-the-bed|co-?living|private room in/i)) flags.push('⚠️ CO-LIVING / room-share');
  if (has(/\bstudent\b.{0,30}(only|\.edu|enroll)/i)) flags.push('⚠️ STUDENTS ONLY');
  if (has(/1-?month minimum|month-to-month/i)) flags.push('⚠️ short-term lease flag');
  return { price, beds, sqft, flags };
}

function verdict(h, c) {
  const issues = [];
  if (h && !h.error) {
    if (h.total >= 100 || h.C >= 30) issues.push('SLUMLORD (HPD ' + h.total + ' open, ' + h.C + ' Class C)');
    else if (h.recent >= 10 && h.C >= 5) issues.push('CAUTION: ' + h.recent + ' recent violations, ' + h.C + ' Class C');
    else if (h.total <= 5) issues.push('clean building');
    else issues.push('mostly old/zombie violations');
  }
  if (c && !c.error) {
    if (c.mins > 50) issues.push('OVER 50-min commute cap (' + c.mins + ')');
    else if (c.mins <= 40) issues.push('great commute (' + c.mins + ')');
  }
  return issues.join(' | ');
}

(async () => {
  const args = process.argv.slice(2);
  const key = loadKey();
  let txt = '', addr = null, ext = null;

  if (args[0] === '--addr') {
    addr = parseAddress(args[1]);
    addr.full = args[1];
  } else {
    const url = args[0];
    console.log('Scraping (a browser window will flash — that is the stealth bypass)...');
    txt = await scrape(url);
    ext = extract(txt);
    addr = parseAddress(txt);
  }

  console.log('\n================ LISTING ================');
  if (ext) console.log(`Price: ${ext.price} | ${ext.beds} | ${ext.sqft}`);
  if (addr) console.log(`Address: ${addr.full}  [HPD key: ${addr.hn} / ${addr.streetname} / ${addr.boro||'?'}]`);
  else { console.log('Could not parse address from page. Re-run with --addr "<full address>".'); if (txt) console.log(txt.slice(0,600)); return; }
  if (ext && ext.flags.length) console.log('Flags: ' + ext.flags.join(' · '));

  const [h, c] = await Promise.all([hpd(addr), commute(addr.full, key)]);

  console.log('\n================ HPD ================');
  if (h.error) console.log(h.error);
  else {
    console.log(`${h.total} open (${h.C}C / ${h.B}B / ${h.A}A / ${h.I}I), ${h.recent} recent (2023+)`);
    h.recentSerious.forEach(s => console.log('  ' + s));
  }

  console.log('\n================ COMMUTE (Mon 8:30am → 1 MW) ================');
  if (c.error) console.log(c.error);
  else { console.log(`${c.mins} min`); c.legs.forEach(l => console.log('  ' + l)); }

  console.log('\n================ VERDICT ================');
  console.log(verdict(h, c));
})();
