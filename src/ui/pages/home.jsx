import { useState, useEffect } from 'preact/hooks';
import { DRILLS, NAV } from '../registry.jsx';
import { allStats, mocks, subscribe } from '../store.js';
import { Btn, Mastery, cx } from '../kit.jsx';
import { CODE } from '../../engines/tmcode.js';
import { activeMock } from './mock.jsx';
import { CLAUDE_URL } from '../host.js';

// The overview answers, in order: what is this and where do I start (first visit, often from a
// shared link); what is worth the most marks (short on time); what next and how am I doing
// (returning); and when, where, what to bring (the night before). Everything else is a click away.

const TEST_AT = Date.UTC(2026, 9, 14, 5, 15, 0); // Wed 14 Oct 2026, 6:15 pm NZDT (UTC+13)
const HOUR = 3600000;
const YEARS = [2023, 2024, 2025];
const go = (id, preset) => window.__openDrill(id, preset);

// Marks per question type in the 2023, 2024 and 2025 Test 2 papers (40 marks each).
const PLAN = [
  { what: 'Induction proofs', detail: 'ordinary and strong', short: 'induction proofs', y: [10, 11, 6], drills: ['i-proof', 'i-strong'] },
  { what: 'Regular grammar ↔ automaton', detail: 'NFSA or DFSA, with a derivation', short: 'grammars and automata', y: [5, 3, 7], drills: ['g-reg2nfsa', 'g-fa2reg'] },
  { what: 'Predicate logic translation', detail: 'both ways', short: 'predicate logic', y: [4, 4, 5], drills: ['q-translate', 'q-english'] },
  { what: 'Halting problem & universal TMs', detail: 'explained in words', short: 'the halting problem', y: [4, 3, 4], drills: ['tm-theory'] },
  { what: 'Truth tables & logical status', detail: 'equivalence, functional completeness', short: 'truth tables', y: [1, 5, 4], drills: ['p-table', 'p-dnf', 'p-laws'] },
  { what: 'Derivation & parse tree', detail: 'and describe L(G)', short: 'derivations', y: [0, 4, 5], drills: ['g-derive'] },
  { what: 'Undecidable problems & the hierarchy', detail: 'true or false', short: 'the hierarchy', y: [2, 4, 2], drills: ['g-classify', 'tm-theory'] },
  { what: 'Decode a Turing number', detail: 'the first 60 bits', short: 'Turing numbers', y: [0, 4, 4], drills: ['tm-decode', 'tm-encode'] },
  { what: 'NAND-only rewrite', short: 'NAND rewrites', y: [4, 0, 3], drills: ['p-nand'] },
  { what: 'Design a grammar', detail: 'or a non-context-free example', short: 'grammar design', y: [4, 2, 0], drills: ['g-design', 'g-cs'] },
  { what: 'Argument validity', detail: 'English → WFF', short: 'argument validity', y: [6, 0, 0], drills: ['p-argue'] },
];
// Weight per paper (2023, 2024, 2025): 2025 is the closest to this year's test, so it counts double.
const WEIGHT = [1, 1, 2];
const avg = (r) => r.y.reduce((s, x, k) => s + x * WEIGHT[k], 0) / WEIGHT.reduce((s, w) => s + w, 0);
// Highest weighted average first; ties go to whichever counted for more in the most recent paper.
const RANKED = [...PLAN].sort((a, b) => avg(b) - avg(a) || b.y[2] - a.y[2] || b.y[1] - a.y[1]);
const TOP = 5;
const MAX_AVG = avg(RANKED[0]);
const in2025 = (rows) => rows.reduce((s, r) => s + r.y[2], 0);
const TOP_2025 = in2025(RANKED.slice(0, TOP));
const REST_2025 = in2025(RANKED.slice(TOP));
const fmtAvg = (a) => (Math.abs(a - Math.round(a)) < 0.05 ? String(Math.round(a)) : a.toFixed(1));
// Suggested order: the plan's drills by marks, then the supporting drills in the sidebar's order.
// (Built on first use: the registry imports this module, so DRILLS and NAV aren't ready at load.)
let order = null;
const drillOrder = () => (order ||= [...new Set([...RANKED.flatMap((r) => r.drills), ...NAV.flatMap((g) => g.items)])].filter((id) => DRILLS[id]));

const fmtScore = (x) => (Number.isInteger(x) ? String(x) : String(Math.round(x * 2) / 2));
const plural = (n, w) => `${n} ${w}${n === 1 ? '' : 's'}`;

function useNow(ms) {
  const [now, setNow] = useState(Date.now());
  useEffect(() => { const t = setInterval(() => setNow(Date.now()), ms); return () => clearInterval(t); }, []);
  return now;
}

// "Today" / "Tomorrow" in New Zealand time, where the test is.
function relDay(now) {
  try {
    const key = (t) => new Intl.DateTimeFormat('en-CA', { timeZone: 'Pacific/Auckland', year: 'numeric', month: '2-digit', day: '2-digit' }).format(t);
    const k = key(TEST_AT);
    if (key(now) === k) return 'Today';
    if (key(now + 24 * HOUR) === k) return 'Tomorrow';
  } catch { /* no time-zone data */ }
  return null;
}

function Tape({ text }) {
  return (
    <div class="tape" aria-hidden="true">
      {[...text].map((ch, i) => (
        <div key={i} class="tape-cell">
          {[...(CODE[ch] || '00000')].map((b, j) => <span key={j} class={cx('tape-hole', b === '1' && 'on')} />)}
        </div>
      ))}
    </div>
  );
}

// ---------------------------------------------------------------- test card
function TestCard({ now }) {
  const left = TEST_AT - now;
  // On phones the logistics fold away behind one tap, except in the last 30 hours when they matter most.
  const [more, setMore] = useState(false);
  const forced = left > 0 && left <= 30 * HOUR;
  const open = more || forced;
  const mins = Math.max(0, Math.ceil(left / 60000));
  const d = Math.floor(mins / 1440), h = Math.floor((mins % 1440) / 60), m = mins % 60;
  const rel = relDay(now);
  let count;
  if (left > 0) {
    count = (
      <div class="tk-count" aria-label={`${plural(d, 'day')}, ${plural(h, 'hour')} and ${plural(m, 'minute')} to go`}>
        {d > 0 && <span><b>{d}</b><small>{d === 1 ? 'day' : 'days'}</small></span>}
        {(d > 0 || h > 0) && <span><b>{h}</b><small>{h === 1 ? 'hr' : 'hrs'}</small></span>}
        <span><b>{m}</b><small>min</small></span>
        <span class="tk-togo">to go</span>
      </div>
    );
  } else if (left > -HOUR) count = <div class="tk-now">Under way now. Good luck!</div>;
  else count = <div class="tk-now">Test 2 has been sat.</div>;
  return (
    <aside class={cx('ticket', open && 'open')} aria-label="Test 2 details">
      <div class="tk-top">
        <div class="tk-row">
          <span class="tk-label">Test 2</span>
          <span title="14/10, punched in the course’s Turing code"><Tape text="14/10" /></span>
        </div>
        <div class="tk-date">{rel && left > -HOUR ? `${rel}, ` : 'Wednesday '}14 October · 6:15 pm</div>
        <div class="tk-format">60 minutes · 40 marks · worth 15%</div>
        {count}
      </div>
      {!forced && (
        <button type="button" class="tk-toggle" aria-expanded={open} aria-controls="tk-list" onClick={() => setMore(!more)}>
          Rooms, rules and what’s supplied<span class={cx('chev', open && 'up')} aria-hidden="true" />
        </button>
      )}
      <dl class="tk-list" id="tk-list">
        <div><dt>Rooms</dt><dd>L.G.02 · surnames A–L<br />L.G.03 · surnames M–Z</dd></div>
        <div><dt>Covers</dt><dd>Weeks 5–9: universal TMs to strong induction</dd></div>
        <div><dt>Be ready</dt><dd>By 6:10 pm, ID face up</dd></div>
        <div><dt>Not allowed</dt><dd>Calculators, red pens</dd></div>
        <div><dt>Supplied</dt><dd>Turing code table, laws of equivalence <span class="nowrap">(<button type="button" class="linkish" onClick={() => go('ref')}>see them</button>)</span></dd></div>
      </dl>
    </aside>
  );
}

// ---------------------------------------------------------------- study plan
function PlanRow({ r, rank, st, next }) {
  const mastered = r.drills.every((d) => (st[d]?.clean || 0) >= 3);
  const started = r.drills.some((d) => (st[d]?.solved || 0) > 0);
  const a = avg(r);
  return (
    <li class={cx('plan-row', mastered ? 'done' : started && 'started', r.drills.includes(next) && 'has-next')}>
      <span class="plan-rank" aria-hidden="true">{mastered ? '✓' : rank}</span>
      <div class="plan-what">
        <span class="plan-name">{r.what}</span>
        {r.detail && <span class="plan-detail">{r.detail}</span>}
        {mastered && <span class="sr-only"> (mastered)</span>}
      </div>
      <div class="plan-nums">
        <span class="sr-only">{`Marks: ${r.y.map((x, k) => `${x} in ${YEARS[k]}`).join(', ')}; ${fmtAvg(a)} weighted average, with 2025 counted double.`}</span>
        <span class="plan-bar" aria-hidden="true"><span style={{ width: `${Math.max(4, (a / MAX_AVG) * 100)}%` }} /></span>
        <span class="plan-avg" aria-hidden="true">{fmtAvg(a)}</span>
        <span class="plan-years" aria-hidden="true">{r.y.map((x, k) => <span key={k} class={cx('yr', !x && 'none')} title={`${YEARS[k]}: ${x ? plural(x, 'mark') : 'not asked'}`}>{x || '–'}</span>)}</span>
      </div>
      <div class="plan-drills">
        {r.drills.map((d) => (
          <button type="button" key={d} class={cx('drill-chip', d === next && 'next')} onClick={() => go(d)}>
            {d === next && <span class="next-tag">Next</span>}
            <span>{DRILLS[d].title}</span>
            <Mastery id={d} />
          </button>
        ))}
      </div>
    </li>
  );
}

function Plan({ st, next }) {
  // Where the suggestion sits; tm-theory is in two rows, so only the first one gets the marker.
  const nextRow = RANKED.findIndex((r) => r.drills.includes(next));
  const topDone = RANKED.slice(0, TOP).every((r) => r.drills.every((d) => (st[d]?.clean || 0) >= 3));
  const [all, setAll] = useState(() => topDone);
  const rows = all ? RANKED : RANKED.slice(0, TOP);
  return (
    <div class="card plan">
      <div class="plan-head" aria-hidden="true">
        <span class="ph-q">Question type</span>
        <span class="plan-nums">
          <span class="ph-avg">Weighted average</span>
          <span class="plan-years">{YEARS.map((y) => <span key={y}>{y}</span>)}</span>
        </span>
      </div>
      <ol class="plan-list">
        {rows.map((r, i) => <PlanRow key={r.what} r={r} rank={i + 1} st={st} next={i === nextRow ? next : null} />)}
      </ol>
      <div class="plan-foot">
        <button type="button" class="btn ghost sm" aria-expanded={all} onClick={() => setAll(!all)}>
          {all ? 'Show only the top five' : `Show ${RANKED.length - TOP} more question types (${REST_2025} marks in 2025)`}
          <span class={cx('chev', all && 'up')} aria-hidden="true" />
        </button>
        <button type="button" class="btn ghost sm only-narrow" onClick={() => window.dispatchEvent(new Event('t2:open-drills'))}>Browse all {Object.keys(DRILLS).length} drills</button>
        <span class="plan-legend"><span class="dots"><span class="dot on" /><span class="dot on" /><span class="dot on" /></span> mastered: three solves without hints</span>
      </div>
    </div>
  );
}

// ---------------------------------------------------------------- page
function SecHead({ n, id, title, children }) {
  return (
    <div class="sec-head">
      <span class="sec-num" aria-hidden="true">{n}</span>
      <h2 class="sec-title" id={id}>{title}</h2>
      {children && <p class="sec-sub">{children}</p>}
    </div>
  );
}

function MockBanner({ mock }) {
  const mins = Math.max(1, Math.ceil(mock.left / 60000));
  return (
    <div class="home-banner" role="status">
      <span class="grow">
        <strong>{mock.over ? 'Your mock test’s time is up.' : 'You have a mock test in progress.'}</strong>{' '}
        {mock.over ? 'It’s marked as soon as you open it.' : mock.timed ? `${plural(mins, 'minute')} left on the clock.` : 'It’s untimed, so carry on whenever you like.'}
      </span>
      <Btn kind="primary" sm onClick={() => go('mock')}>{mock.over ? 'See your results' : 'Resume'}</Btn>
    </div>
  );
}

export function HomePage() {
  const now = useNow(15000);
  const [, force] = useState(0);
  useEffect(() => subscribe(() => force((x) => x + 1)), []);
  const st = allStats();
  const past = mocks();
  const mock = activeMock(now);
  const ids = Object.keys(DRILLS);
  const isNew = !ids.some((id) => (st[id]?.solved || 0) > 0) && past.length === 0;
  const mastered = ids.filter((id) => (st[id]?.clean || 0) >= 3).length;
  const next = drillOrder().find((id) => (st[id]?.clean || 0) < 3) || null;
  const lastId = ids.filter((id) => st[id]?.last).sort((a, b) => st[b].last - st[a].last)[0];
  const left = TEST_AT - now;
  const lastMock = past.slice(-1)[0];

  // One primary action, chosen for where the student is.
  const mockAct = mock ? { label: mock.over ? 'See your mock results' : 'Resume your mock test', run: () => go('mock') } : { label: 'Take a mock test', run: () => go('mock') };
  const nextAct = next && { label: isNew ? `Start with ${RANKED[0].short}` : `Next up: ${DRILLS[next].title}`, run: () => go(next) };
  const nightBefore = left > 0 && left <= 30 * HOUR && !mock && !past.some((m) => now - m.at < 30 * HOUR);
  let primary, secondary;
  if (nightBefore) [primary, secondary] = [{ label: 'Sit a timed mock test', run: () => go('mock') }, nextAct || { label: 'Past papers', run: () => go('papers') }];
  else if (!next) [primary, secondary] = [mockAct, { label: 'Past papers', run: () => go('papers') }];
  else [primary, secondary] = [nextAct, mockAct];

  return (
    <div class="sheet home">
      {mock && <MockBanner mock={mock} />}

      <section class="home-hero">
        <div class="home-intro">
          <div class="h-kicker">COMPX361-26B Logic and Computation · Test 2</div>
          <h1 class="home-title">Every Test 2 process, one checked step at a time.</h1>
          <p class="home-sub">Drills that check each line as you write it, the 2023–25 papers with the lecturer’s solutions, and a timed mock test.</p>
          <div class="home-cta">
            <Btn kind="primary" onClick={primary.run}>{primary.label}<span aria-hidden="true">→</span></Btn>
            <Btn onClick={secondary.run}>{secondary.label}</Btn>
          </div>
          <p class="home-meta">
            {isNew ? 'No sign-up: your progress is saved in this browser.' : (
              <>
                {mastered} of {ids.length} drills mastered
                {lastId && lastId !== next && <> · Last practised: <button type="button" class="linkish" onClick={() => go(lastId)}>{DRILLS[lastId].title}</button></>}
              </>
            )}
          </p>
        </div>
        <TestCard now={now} />
      </section>

      <section class="home-sec" aria-labelledby="sec-plan">
        <SecHead n={1} id="sec-plan" title="Drill the processes, highest marks first">
          Ranked by marks in the 2023–25 papers, with 2025 counted double. The top five made up {TOP_2025} of the 40 marks in 2025.
        </SecHead>
        <Plan st={st} next={next} />
      </section>

      <div class="home-pair">
        <section class="card home-card" aria-labelledby="sec-papers">
          <SecHead n={2} id="sec-papers" title="Check yourself on past papers" />
          <p class="muted">Every question from the last three tests and tutorials 5–9, with the lecturer’s own solutions and mark allocations.</p>
          <div class="row">
            {['2025', '2024', '2023'].map((y) => <Btn key={y} onClick={() => go('papers', { tab: y })}>{y} test</Btn>)}
            <Btn kind="ghost" onClick={() => go('papers', { tab: 'tut5' })}>Tutorials</Btn>
          </div>
        </section>
        <section class="card home-card" aria-labelledby="sec-mock">
          <SecHead n={3} id="sec-mock" title="Rehearse under test conditions" />
          <p class="muted">A fresh 60-minute, 40-mark paper in the format of a past test, marked when you submit. Best done the night before.</p>
          <div class="row">
            <Btn onClick={() => go('mock')}>{mock ? (mock.over ? 'See your results' : 'Resume your mock test') : 'Start a mock test'}</Btn>
            {lastMock && !mock && (
              <span class="small muted">Last time: <strong>{fmtScore(lastMock.score)} / {lastMock.max}</strong>{lastMock.pending ? ` (+${fmtScore(lastMock.pending)} unmarked)` : ''}, {new Date(lastMock.at).toLocaleDateString(undefined, { weekday: 'short', day: 'numeric', month: 'short' })}</span>
            )}
          </div>
        </section>
      </div>

      <footer class="home-foot">
        <p>Every step is checked as you go: truth-table cells, each law in a proof, every line of induction working, each derivation step, and each grammar against every short string.{CLAUDE_URL
          ? <> Written answers are marked against a checklist here; <a href={CLAUDE_URL} target="_blank" rel="noopener">open the trainer in Claude</a> to have Claude mark them through your own Claude account.</>
          : ' Written answers can be marked by Claude through your own Claude account (it asks first); otherwise you mark them against a checklist.'}</p>
        <p>An unofficial study aid made from the COMPX361 notes, tutorials and past tests; not produced or checked by the course staff.</p>
      </footer>
    </div>
  );
}
