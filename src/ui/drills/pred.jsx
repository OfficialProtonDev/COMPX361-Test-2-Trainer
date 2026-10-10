import { useState, useMemo, useEffect } from 'preact/hooks';
import { parsePred, tryParsePred, showPred, comparePred, describeWorld, checkPushStep, pushAll, keyPred } from '../../engines/pred.js';
import { SCENARIOS, SCENARIO_IDS, sentences, NUMBER_FACTS } from '../../data/predbank.js';
import { Rng } from '../../engines/rng.js';
import { MathText, Btn, Seg, Chip, Fb, MathField, Step, Options, DrillHeader, useSolve, useSeed, ModelAnswer, SolvedBanner, cx, Collapse } from '../kit.jsx';

function ScenarioBox({ scen }) {
  return <div class="panel small">{scen.setup}</div>;
}

// ---------------------------------------------------------------- English → logic
export function TranslateDrill({ preset }) {
  const id = 'q-translate';
  const [scenId, setScenId] = useState(preset?.scen || 'dogs');
  const [lvl, setLvl] = useState(0);
  const [seed, next] = useSeed(preset?.seed);
  const scen = SCENARIOS[scenId];
  // some scenarios have no sentences of a level (no “at least two” crows): fall back to all of them
  const pool = useMemo(() => { const p = sentences(scenId).filter((s) => !lvl || s.lvl === lvl); return p.length ? p : sentences(scenId); }, [scenId, lvl]);
  const emptyLevel = lvl && !sentences(scenId).some((s) => s.lvl === lvl);
  const item = useMemo(() => {
    if (preset?.sid && seed === preset.seed) return pool.find((s) => s.id === preset.sid) || pool[0];
    return new Rng(seed).pick(pool);
  }, [seed, pool]);
  const [input, setInput] = useState('');
  const [msg, setMsg] = useState(null);
  const [streak, setStreak] = useState(0);
  const S = useSolve(id, seed + scenId + lvl);
  useEffect(() => { setInput(''); setMsg(null); }, [item]);
  const check = () => {
    const p = tryParsePred(input);
    if (!p.ok) { setMsg({ kind: 'bad', text: p.error }); return; }
    const r = comparePred(p.ast, parsePred(item.f), scen.sig);
    if (r.error) { setMsg({ kind: 'bad', text: r.error }); return; }
    if (r.equiv) {
      setMsg({ kind: 'good', text: 'Correct: true in exactly the same situations.' + (r.free.length ? ` (Your free variable${r.free.length > 1 ? 's' : ''} ${r.free.join(', ')} ${r.free.length > 1 ? 'are' : 'is'} read as “for all”; the 2024 solutions accept that, but quantifying is safer.)` : '') });
      setStreak((s) => s + 1); S.finish();
    } else {
      setMsg({ kind: 'bad', text: `Not the same meaning. ${describeWorld(r.world, scen)} In that world the sentence is ${r.ref ? 'true' : 'false'}, but your formula is ${r.user ? 'true' : 'false'}.` });
      setStreak(0);
    }
  };
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Predicate logic · PRED1, PRED2" title="English → predicate logic"
        sub="Your formula is tested against the intended meaning in every small world (up to 3 of each kind of thing). If they differ you’ll see a world where they disagree.">
        <select class="input" style={{ width: 'auto' }} value={scenId} onChange={(e) => { setScenId(e.currentTarget.value); next(); }} aria-label="Scenario">{SCENARIO_IDS.map((s) => <option key={s} value={s}>{SCENARIOS[s].title}</option>)}</select>
        <Seg value={lvl} onChange={(v) => { setLvl(v); next(); }} label="Difficulty" options={[{ value: 0, label: 'All' }, { value: 1, label: 'Basic' }, { value: 2, label: 'Negations' }, { value: 3, label: '“At least two”, “exactly one”' }]} />
        <Btn onClick={next}>New sentence</Btn>
        {streak > 1 && <Chip kind="good">{streak} in a row</Chip>}
      </DrillHeader>
      {emptyLevel ? <Fb kind="info">This scenario has no sentences of that kind, so here are all of its sentences.</Fb> : null}
      <div class="question">
        <div class="qmeta"><Chip kind="marks">1 mark each</Chip></div>
        <ScenarioBox scen={scen} />
        <div class="qtext" style={{ fontSize: '19px' }}>“{item.en}”</div>
      </div>
      <div class="card stack">
        <MathField id="tr-in" kind="pred" value={input} setValue={setInput} onEnter={check} placeholder={scen.sig.sorts.length > 1 ? 'e.g. ∀x ∃y : P(x, y)' : scenId === 'crows' ? 'e.g. ∀x : P(x) → Q(x)' : 'e.g. ∃x ∀y : P(x, y)'} extraSyms={scen.sig.sorts.length > 1 ? ['∈', 'X', 'Y', 'P(x, y)'] : scenId === 'crows' ? ['P(x)', 'Q(x)'] : ['P(x, y)']} />
        <div class="step-actions"><Btn kind="primary" onClick={check}>Check</Btn><Btn kind="ghost" onClick={() => { S.reveal(); setInput(item.f); }}>Show the answer</Btn></div>
        {msg && <Fb kind={msg.kind}>{msg.text}</Fb>}
        {(S.solved || S.revealed) && <ModelAnswer title="Model answer"><MathText text={item.f} block /></ModelAnswer>}
        {S.solved && <SolvedBanner clean={!S.revealed} onNext={next} />}
      </div>
      <Collapse title="Translation patterns that come up every year">
        <table class="plain"><tbody>
          {[['All A are B', '∀x : A(x) → B(x)'], ['Some A are B', '∃x : A(x) ∧ B(x)'], ['No A is B', '¬∃x : A(x) ∧ B(x)   ⇔   ∀x : A(x) → ¬B(x)'], ['Every x has some y', '∀x ∃y : P(x, y)'], ['Some x has every y', '∃x ∀y : P(x, y)'], ['x has no y', '¬∃y : P(x, y)   ⇔   ∀y : ¬P(x, y)'], ['at least two different y', '∃y ∃z : P(x, y) ∧ P(x, z) ∧ (y ≠ z)']].map(([a, b]) => <tr key={a}><td>{a}</td><td><MathText text={b} /></td></tr>)}
        </tbody></table>
      </Collapse>
    </div>
  );
}

// ---------------------------------------------------------------- logic → English
export function disguise(ast, rng) {
  // replace one quantifier Qx φ with ¬Q'x ¬φ (pushing the inner ¬ one level), like the past papers do
  const qs = [];
  (function walk(n, path) { if (n.t === 'q') { qs.push(path); walk(n.body, [...path, 'body']); } else if (n.t === 'not') walk(n.a, [...path, 'a']); })(ast, []);
  if (!qs.length) return ast;
  const path = rng.pick(qs);
  const rebuild = (n, p) => {
    if (!p.length) {
      const inner = n.body.t === 'not' ? n.body.a : { t: 'not', a: n.body };
      return { t: 'not', a: { t: 'q', q: n.q === 'all' ? 'ex' : 'all', v: n.v, dom: n.dom, body: pushOne(inner) } };
    }
    const [h, ...rest] = p;
    return { ...n, [h]: rebuild(n[h], rest) };
  };
  return rebuild(ast, path);
}
function pushOne(n) {
  if (n.t === 'not' && n.a.t === 'q') return { t: 'q', q: n.a.q === 'all' ? 'ex' : 'all', v: n.a.v, dom: n.a.dom, body: n.a.body.t === 'not' ? n.a.body.a : { t: 'not', a: n.a.body } };
  return n;
}

export function EnglishDrill({ preset }) {
  const id = 'q-english';
  const [scenId, setScenId] = useState(preset?.scen || 'dogs');
  const [seed, next] = useSeed();
  const scen = SCENARIOS[scenId];
  const prob = useMemo(() => {
    const rng = new Rng(seed);
    const pool = sentences(scenId).filter((s) => s.lvl <= 2);
    const item = rng.pick(pool);
    let ast = parsePred(item.f);
    if (rng.chance(0.6)) ast = disguise(ast, rng);
    const others = rng.shuffle(pool.filter((s) => s.id !== item.id)).filter((s) => !comparePred(parsePred(s.f), parsePred(item.f), scen.sig).equiv);
    const opts = rng.shuffle([item, ...others.slice(0, 3)]);
    return { item, ast, opts, correct: opts.indexOf(item) };
  }, [seed, scenId]);
  const [pick, setPick] = useState(null);
  const S = useSolve(id, seed + scenId);
  useEffect(() => setPick(null), [prob]);
  useEffect(() => { if (pick === prob.correct) S.finish(); }, [pick]);
  const simplified = showPred(pushAll(prob.ast));
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Predicate logic · PRED2" title="Predicate logic → English"
        sub="“Give simplest possible English sentences.” Push negations inwards first (generalised De Morgan, double negation); the meaning usually jumps out.">
        <select class="input" style={{ width: 'auto' }} value={scenId} onChange={(e) => { setScenId(e.currentTarget.value); next(); }} aria-label="Scenario">{SCENARIO_IDS.map((s) => <option key={s} value={s}>{SCENARIOS[s].title}</option>)}</select>
        <Btn onClick={next}>New formula</Btn>
      </DrillHeader>
      <div class="question">
        <div class="qmeta"><Chip kind="marks">1 mark</Chip></div>
        <ScenarioBox scen={scen} />
        <div class="qtext">Express in simple English: <MathText text={showPred(prob.ast)} /></div>
      </div>
      <div class="card stack">
        <Options options={prob.opts.map((o) => o.en)} picked={pick} onPick={setPick} reveal={pick != null} correct={prob.correct} />
        {pick != null && <Fb kind={pick === prob.correct ? 'good' : 'bad'}>{showPred(prob.ast) !== simplified ? <>Simplify first: <MathText text={`${showPred(prob.ast)}  ⇔  ${simplified}`} />. </> : null}So it says: “{prob.item.en}”</Fb>}
        {pick != null && <SolvedBanner clean={pick === prob.correct} missed={pick !== prob.correct} onNext={next} />}
      </div>
    </div>
  );
}

// ---------------------------------------------------------------- generalised De Morgan
const NEG_BANK = [
  { f: '¬∀x : ¬P(x)', src: 'PRED1 notes (with P(x) = x > 0)' },
  { f: '∃x ¬∃y ∀z : ¬Q(x, y, z)', src: 'PRED2 notes' },
  { f: '¬∀x ∃y : ¬P(x, y)', src: 'Tutorial 8 Q2(a)(iii)' },
  { f: '¬∃y ¬∃x : P(x, y)', src: 'Tutorial 8 Q2(b)(ii)' },
  { f: '∀x ¬∃y : ¬P(x, y)', src: '2025 Test 2 Q9(b)(ii)' },
  { f: '¬∃x ∀y : ¬P(x, y)', src: '2023 Test 2 Q8(b)(ii)' },
  { f: '¬∃x ¬∃y : ¬P(x, y)', src: 'PRED2 notes (with P = x ≤ y)' },
  { f: '¬∀x ¬∀y ∃z : Q(x, y, z)', src: 'practice' },
];

function genericSig(ast) {
  const preds = {};
  (function walk(n) {
    if (n.t === 'atom') preds[n.p] = Array(n.args.length).fill('D');
    if (n.t === 'q') walk(n.body); if (n.t === 'not') walk(n.a); if (n.t === 'bin') { walk(n.a); walk(n.b); }
  })(ast);
  return { sorts: ['D'], preds, domAlias: {} };
}
function negsOk(n) { // negations only directly on atoms
  if (n.t === 'not') return n.a.t === 'atom' || n.a.t === 'eq';
  if (n.t === 'q') return negsOk(n.body);
  if (n.t === 'bin') return negsOk(n.a) && negsOk(n.b);
  return true;
}

export function NegateDrill() {
  const id = 'q-negate';
  const [seed, next] = useSeed();
  const [src, setSrc] = useState('bank');
  const prob = useMemo(() => {
    const rng = new Rng(seed);
    if (src === 'bank') { const b = rng.pick(NEG_BANK); return { ast: parsePred(b.f), src: b.src }; }
    const vs = ['x', 'y', 'z'].slice(0, rng.pick([2, 2, 3]));
    let body = { t: 'atom', p: vs.length === 3 ? 'Q' : 'P', args: vs };
    if (rng.chance(0.5)) body = { t: 'not', a: body };
    let f = body;
    for (let i = vs.length - 1; i >= 0; i--) { f = { t: 'q', q: rng.pick(['all', 'ex']), v: vs[i], dom: null, body: f }; if (rng.chance(0.55)) f = { t: 'not', a: f }; }
    if (negsOk(f)) f = { t: 'not', a: f };
    return { ast: f, src: 'random' };
  }, [seed, src]);
  const target = useMemo(() => pushAll(prob.ast), [prob]);
  const sig = useMemo(() => genericSig(prob.ast), [prob]);
  const [lines, setLines] = useState([]);
  const [input, setInput] = useState('');
  const [msg, setMsg] = useState(null);
  const S = useSolve(id, seed + src);
  useEffect(() => { setLines([]); setInput(''); setMsg(null); }, [prob]);
  const cur = lines.length ? lines[lines.length - 1].ast : prob.ast;
  const done = lines.length && negsOk(cur);
  useEffect(() => { if (done) S.finish(); }, [done]);
  const add = () => {
    const p = tryParsePred(input);
    if (!p.ok) { setMsg({ kind: 'bad', text: p.error }); return; }
    if (keyPred(p.ast) === keyPred(cur)) { setMsg({ kind: 'hint', text: 'That’s the same as the line before. Move a ¬ inwards past the next quantifier.' }); return; }
    const step = checkPushStep(cur, p.ast);
    if (step.ok) { setLines((L) => [...L, { ast: p.ast, why: 'generalised De Morgan / double negation' }]); setInput(''); setMsg({ kind: 'good', text: step.apps > 1 ? `Correct (${step.apps} moves in one line).` : 'Correct.' }); return; }
    const eq = comparePred(p.ast, cur, sig, Object.values(sig.preds).some((a) => a.length > 2) ? 2 : 3);
    if (eq.equiv) { setLines((L) => [...L, { ast: p.ast, why: 'equivalent (uses more than the quantifier laws)' }]); setInput(''); setMsg({ kind: 'hint', text: 'Equivalent, but that isn’t a single use of generalised De Morgan / double negation. In a test, show one move per line.' }); return; }
    setMsg({ kind: 'bad', text: 'That changes the meaning. Moving ¬ past ∀ turns it into ∃ (and vice versa), and the ¬ goes onto what follows.' });
  };
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Predicate logic · PRED1, PRED2" title="Generalised De Morgan"
        sub="¬∀x : P(x) ⇔ ∃x : ¬P(x) and ¬∃x : P(x) ⇔ ∀x : ¬P(x). Push every ¬ inwards until it sits on a predicate, cancelling ¬¬ as you go.">
        <Seg value={src} onChange={(v) => { setSrc(v); next(); }} label="Source" options={[{ value: 'bank', label: 'Notes & tests' }, { value: 'random', label: 'Random' }]} />
        <Btn onClick={next}>New formula</Btn>
      </DrillHeader>
      <div class="question"><div class="qmeta"><Chip kind="src">{prob.src}</Chip></div><div class="qtext">Simplify <MathText text={showPred(prob.ast)} /> so that no ¬ comes before a quantifier.</div></div>
      <div class="card stack">
        <div class="working">
          <div><MathText text={showPred(prob.ast)} /></div>
          {lines.map((l, i) => <div key={i}>⇔ <MathText text={showPred(l.ast)} /><span class="why">({l.why})</span></div>)}
        </div>
        {!done && <>
          <MathField id="neg-in" kind="pred" value={input} setValue={setInput} onEnter={add} placeholder="next line" />
          <div class="step-actions"><Btn kind="primary" onClick={add}>Add line</Btn>
            <Btn kind="ghost" onClick={() => { S.reveal(); setMsg({ kind: 'hint', text: `Target: ${showPred(target)}` }); }}>Show the simplified form</Btn>
            {lines.length > 0 && <Btn kind="ghost" onClick={() => setLines((L) => L.slice(0, -1))}>Undo</Btn>}</div>
        </>}
        {msg && <Fb kind={msg.kind}>{msg.text}</Fb>}
        {done ? <SolvedBanner clean={!S.revealed} onNext={next}>{keyPred(cur) === keyPred(target) ? '' : `The fully simplified form is ${showPred(target)}.`}</SolvedBanner> : null}
      </div>
    </div>
  );
}

// ---------------------------------------------------------------- truth over ℝ, ℕ
export function TruthDrill() {
  const id = 'q-truth';
  const [order, setOrder] = useState(() => new Rng(Date.now() & 0xffff).shuffle(NUMBER_FACTS.map((_, i) => i)));
  const [i, setI] = useState(0);
  const f = NUMBER_FACTS[order[i % order.length]];
  const [ans, setAns] = useState(null);
  const [score, setScore] = useState({ right: 0, total: 0 });
  const S = useSolve(id, i);
  useEffect(() => setAns(null), [i]);
  const answer = (v) => { if (ans !== null) return; setAns(v); setScore((s) => ({ right: s.right + (v === f.truth ? 1 : 0), total: s.total + 1 })); if (v === f.truth) S.finish(); };
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Predicate logic · PRED1, PRED2, tutorial 8" title="True or false over ℝ and ℕ"
        sub="For ∃, one example proves it; for ∀, one counterexample disproves it. Read quantifiers left to right, and remember ℕ = {1, 2, 3, …} in this course.">
        <span class="chip">{score.right} / {score.total}</span>
      </DrillHeader>
      <div class="question"><div class="qmeta"><Chip kind="src">{f.src}</Chip></div><div class="qtext" style={{ fontSize: '20px' }}><MathText text={f.f} /></div></div>
      <div class="card stack">
        <div class="row">
          <Btn kind={ans === true ? (f.truth ? 'primary' : 'danger') : ''} onClick={() => answer(true)}>True</Btn>
          <Btn kind={ans === false ? (!f.truth ? 'primary' : 'danger') : ''} onClick={() => answer(false)}>False</Btn>
        </div>
        {ans !== null && <Fb kind={ans === f.truth ? 'good' : 'bad'}>{f.why}</Fb>}
        {ans !== null && <div class="row"><Btn kind="primary" onClick={() => setI((x) => x + 1)}>Next statement</Btn></div>}
      </div>
    </div>
  );
}
