import { useState, useMemo, useEffect } from 'preact/hooks';
import * as A from '../../engines/algebra.js';
import { BANK, generated, checkChain, checkBase, checkStatement, modelProof, stampBases, checkStampRep, REASONS, sideAt, functionsFor, showE } from '../../engines/induction.js';
import { newSeed } from '../../engines/rng.js';
import { Rng } from '../../engines/rng.js';
import { MathText, Btn, Seg, Chip, Fb, MathField, Step, Options, DrillHeader, useSolve, ModelAnswer, SolvedBanner, cx, Collapse } from '../kit.jsx';
import { WrittenAnswer } from '../marking.jsx';

const GROUPS = [
  ['Sums', (p) => p.kind === 'eq'],
  ['Inequalities', (p) => p.kind === 'ineq'],
  ['Divisibility', (p) => p.kind === 'div'],
  ['Odd and even', (p) => p.kind === 'parity'],
  ['Recurrences (ordinary induction)', (p) => p.kind === 'rec' && !p.strong],
];
const SGROUPS = [
  ['Recurrences (strong induction)', (p) => p.kind === 'rec' && p.strong],
  ['Stamps', (p) => p.kind === 'stamps'],
];

const fmtVal = (v) => A.show(v);
const relSyms = ['=', '≥', '>', '≤', '<'];

function useProblem(strong, preset) {
  const [pid, setPid] = useState(preset?.ind || (strong ? 'strong-2024' : 'ineq-2025'));
  const [genSeed, setGenSeed] = useState(newSeed());
  const prob = useMemo(() => {
    if (pid.startsWith('gen:')) return generated(pid.slice(4), genSeed);
    return BANK.find((p) => p.id === pid) || BANK[0];
  }, [pid, genSeed]);
  return { prob, pid, setPid, regen: () => setGenSeed(newSeed()) };
}

function ProblemPicker({ strong, pid, setPid, regen }) {
  const groups = strong ? SGROUPS : GROUPS;
  return (
    <>
      <select class="input" style={{ width: 'auto', minWidth: '260px', maxWidth: '100%' }} value={pid} onChange={(e) => setPid(e.currentTarget.value)} aria-label="Problem">
        {groups.map(([name, f]) => <optgroup key={name} label={name}>{BANK.filter(f).map((p) => <option key={p.id} value={p.id}>{p.title} · {p.src}</option>)}</optgroup>)}
        <optgroup label="Generated">
          {!strong && <option value="gen:div">Random divisibility proof</option>}
          {strong && <option value="gen:recur">Random recurrence (closed form)</option>}
          {strong && <option value="gen:stamps">Random stamp problem</option>}
        </optgroup>
      </select>
      {pid.startsWith('gen:') && <Btn onClick={regen}>New numbers</Btn>}
    </>
  );
}

// ---------------------------------------------------------------- the proof builder
export function ProofBuilder({ prob, drillId }) {
  const S = useSolve(drillId, prob.id + (prob.ask || ''));
  const strong = !!prob.strong;
  const kind = prob.kind;
  const [st, setSt] = useState({});
  const [msgs, setMsgs] = useState({});
  const [done, setDone] = useState({});
  const [firstTry, setFirstTry] = useState({});
  const [tries, setTries] = useState({});
  const [chain, setChain] = useState([{ e: '' }]);
  const [chainRes, setChainRes] = useState(null);
  useEffect(() => { setSt({}); setMsgs({}); setDone({}); setFirstTry({}); setTries({}); setChain([{ e: '' }]); setChainRes(null); }, [prob]);
  const set = (k) => (v) => setSt((s) => ({ ...s, [k]: typeof v === 'function' ? v(s[k] || '') : v }));
  const pass = (k, msg) => { setDone((d) => ({ ...d, [k]: true })); setMsgs((m) => ({ ...m, [k]: { kind: 'good', text: msg || 'Correct.' } })); setFirstTry((f) => (f[k] === undefined ? { ...f, [k]: !(tries[k] > 0) } : f)); };
  const fail = (k, text) => { setMsgs((m) => ({ ...m, [k]: { kind: 'bad', text } })); setTries((t) => ({ ...t, [k]: (t[k] || 0) + 1 })); };
  const reveal = (k, fill) => { S.reveal(); setSt((s) => ({ ...s, ...fill })); setFirstTry((f) => ({ ...f, [k]: false })); };
  const n0 = prob.n0;
  const nbWanted = prob.nb || 1;
  const nbOk = (v) => (prob.id === 'strong-t9q4' ? v === 2 || v === 3 : v === nbWanted);
  const nbChosen = Number(st.nb) || nbWanted;
  const kmin = n0 + (strong ? nbChosen : 1) - 1;
  const evalAt = (expr, x) => A.evaluate(A.parseExpr(expr), { n: A.Q(x), k: A.Q(x) }, functionsFor(prob));
  const sameExpr = (userText, targetExpr, varName = 'n', offset = 0) => {
    try {
      const u = A.parseExpr(userText);
      for (let x = 2; x < 9; x++) {
        const a = A.evaluate(u, { [varName]: A.Q(x) }, functionsFor(prob));
        const b = A.evaluate(A.parseExpr(targetExpr), { n: A.Q(x + offset) }, functionsFor(prob));
        if (A.cmp(a, b) !== 0) return false;
      }
      return true;
    } catch { return false; }
  };

  // ---- step 1: predicate
  const check1 = () => {
    if (Number(st.n0) !== n0) { fail('p', `Which is the first n the question asks about? (“n > 1” means n ≥ 2.)`); return; }
    if (kind === 'div') {
      if (!sameExpr(st.pe || '', prob.div.expr)) { fail('p', 'That expression isn’t the one in the question.'); return; }
      if (Number(st.pd) !== prob.div.d) { fail('p', 'Check the divisor.'); return; }
    } else if (kind === 'parity') {
      if (!sameExpr(st.pe || '', prob.parity.expr)) { fail('p', 'That expression isn’t the one in the question.'); return; }
      if ((st.pp || 'odd') !== (prob.parity.odd ? 'odd' : 'even')) { fail('p', 'Odd or even?'); return; }
    } else if (kind === 'stamps') {
      const pair = [Number(st.pa), Number(st.pb)].sort((x, y) => x - y);
      if (pair[0] !== prob.stamps.a || pair[1] !== prob.stamps.b) { fail('p', `Use the two stamp values, ${prob.stamps.a} and ${prob.stamps.b}.`); return; }
    } else {
      const r = checkStatement(prob, st.ps || '', 'n');
      if (!r.ok) { fail('p', r.message); return; }
    }
    pass('p', 'That’s the predicate. Writing it out like this is worth about ½ mark on its own.');
  };
  // ---- step 2: base cases
  const bases = kind === 'stamps' ? stampBases({ ...prob }) : Array.from({ length: strong ? nbChosen : 1 }, (_, i) => ({ n: n0 + i }));
  const check2 = () => {
    if (strong && !nbOk(Number(st.nb))) {
      fail('b', kind === 'stamps' ? `You need as many base cases as the size of the smaller stamp: the step uses P(k + 1 − ${prob.stamps.a}).` : 'The step uses P(k) and P(k − 1), so it needs two consecutive base cases.');
      return;
    }
    for (const b of bases) {
      if (kind === 'stamps') {
        const r = checkStampRep(prob, b.n, st['bx' + b.n], st['by' + b.n]);
        if (!r.ok) { fail('b', `P(${b.n}): ${r.message}`); return; }
      } else if (kind === 'div') {
        const v = evalAt(prob.div.expr, b.n);
        let uv, uq;
        try { uv = A.evaluate(A.parseExpr(st['bv' + b.n] || ''), {}); uq = A.evaluate(A.parseExpr(st['bq' + b.n] || ''), {}); } catch { fail('b', 'Use numbers in the base case.'); return; }
        if (A.cmp(uv, v) !== 0) { fail('b', `Substitute n = ${b.n} into ${showE(prob.div.expr)} again.`); return; }
        if (A.cmp(A.mul(uq, A.Q(prob.div.d)), v) !== 0) { fail('b', `${fmtVal(v)} = ? × ${prob.div.d}`); return; }
      } else if (kind === 'parity') {
        const v = evalAt(prob.parity.expr, b.n);
        let uv;
        try { uv = A.evaluate(A.parseExpr(st['bv' + b.n] || ''), {}); } catch { fail('b', 'Use numbers in the base case.'); return; }
        if (A.cmp(uv, v) !== 0) { fail('b', `Substitute n = ${b.n} again.`); return; }
      } else {
        const r = checkBase(prob, b.n, st['bi' + b.n] || '');
        if (!r.ok) { fail('b', r.message); return; }
      }
    }
    pass('b', bases.length > 1 ? 'All base cases check out.' : 'Base case done.');
  };
  // ---- step 3: hypothesis
  const check3 = () => {
    if (Number(st.hk) !== kmin) { fail('h', strong ? `With base cases ${bases.map((b) => b.n).join(', ')}, the step must start at k = ${kmin} (the last base case).` : `k starts where n starts: k ≥ ${n0}.`); return; }
    if (!strong) {
      if (kind === 'div') {
        if (!sameExpr(st.he || '', prob.div.expr, 'k')) { fail('h', 'Write P(k): the same expression with k in place of n.'); return; }
      } else if (kind === 'parity') {
        if (!sameExpr(st.he || '', prob.parity.expr, 'k')) { fail('h', 'Write P(k): the same expression with k in place of n.'); return; }
      } else {
        const r = checkStatement(prob, st.hs || '', 'k');
        if (!r.ok) { fail('h', r.message); return; }
      }
    }
    pass('h', strong ? 'Right: in strong induction you assume every earlier case.' : 'That’s the inductive hypothesis.');
  };
  // ---- step 4: goal
  const check4 = () => {
    if (kind === 'div') {
      if (!sameExpr(st.ge || '', prob.div.expr, 'k', 1)) { fail('g', 'Replace every n by (k + 1).'); return; }
    } else if (kind === 'parity') {
      if (!sameExpr(st.ge || '', prob.parity.expr, 'k', 1)) { fail('g', 'Replace every n by (k + 1).'); return; }
    } else if (kind !== 'stamps') {
      const r = checkStatement(prob, st.gs || '', 'k+1');
      if (!r.ok) { fail('g', r.message); return; }
    }
    pass('g', 'That’s what you have to prove.');
  };
  // ---- step 5: working
  const runChain = () => {
    const lines = chain.filter((l, i) => i === 0 || (l.e || '').trim());
    if (!lines[0].e?.trim()) { setChainRes({ results: [{ ok: false, message: 'Start with the left-hand side of P(k + 1).' }], overall: null }); return; }
    const r = checkChain(prob, lines.map((l, i) => ({ e: l.e, rel: i === 0 ? '=' : l.rel || '=', why: l.why || 'alg' })));
    setChainRes(r);
    setTries((t) => ({ ...t, w: (t.w || 0) + (r.overall?.ok ? 0 : 1) }));
    if (r.overall?.ok) pass('w', r.overall.message);
  };
  const hintLine = () => {
    S.reveal();
    setFirstTry((f) => ({ ...f, w: false }));
    const filled = chain.filter((l) => (l.e || '').trim()).length;
    if (filled === 0) { setChain([{ e: prob.lhs1 }]); return; }
    const c = prob.chain[filled - 1];
    if (!c) return;
    setChain((C) => [...C.filter((l) => (l.e || '').trim()), { rel: c.rel, e: c.e, why: c.why }]);
  };
  // stamps step
  const checkStampStep = () => {
    const { a } = prob.stamps;
    if (Number(st.sa) !== a) { fail('w', `Peel off one ${a}-cent stamp: k + 1 = (k + 1 − ${a}) + ${a}.`); return; }
    if (Number(st.sl) !== n0) { fail('w', `k + 1 − ${a} must be at least ${n0} so that the hypothesis covers it.`); return; }
    const okX = (() => { try { const e = A.parseExpr(st.sx || ''); for (const [x, y] of [[0, 0], [2, 5], [7, 1]]) { if (A.cmp(A.evaluate(e, { x: A.Q(x), y: A.Q(y), a: A.Q(x), b: A.Q(y) }), A.Q(x + 1)) !== 0) return false; } return true; } catch { return false; } })();
    const okY = (() => { try { const e = A.parseExpr(st.sy || ''); for (const [x, y] of [[0, 0], [2, 5], [7, 1]]) { if (A.cmp(A.evaluate(e, { x: A.Q(x), y: A.Q(y), a: A.Q(x), b: A.Q(y) }), A.Q(y)) !== 0) return false; } return true; } catch { return false; } })();
    if (!okX || !okY) { fail('w', `k + 1 = ${a}x + ${prob.stamps.b}y + ${a} = ${a}(?) + ${prob.stamps.b}(?)`); return; }
    pass('w', 'And x + 1, y are non-negative integers, so P(k + 1) is true.');
  };
  // ---- step 6: conclusion
  const check6 = () => {
    if ((st.cp || '') !== (strong ? 'strong' : 'weak')) { fail('c', strong ? 'You assumed all of P(n₀), …, P(k): that is the second principle of induction (strong induction).' : 'You only used P(k): that is the (first) principle of induction.'); return; }
    if (Number(st.cn) !== n0) { fail('c', `For all n ≥ ${n0}.`); return; }
    pass('c', 'Proof complete.');
    S.finish();
  };
  const allDone = ['p', 'b', 'h', 'g', 'w', 'c'].every((k) => done[k]);
  const stepState = (k, prev) => (!prev ? 'locked' : done[k] ? (firstTry[k] === false ? 'revealed' : 'done') : 'active');
  const marks = [['Predicate', 'p', 0.5], ['Base case(s)', 'b', 0.5], ['Hypothesis', 'h', 0.5], ['Goal + working', 'w', 3], ['Conclusion', 'c', 0.5]];

  return (
    <div class="steps">
      <Step n={1} title="Define the predicate P(n)" state={stepState('p', true)}>
        <div class="row" style={{ alignItems: 'center' }}>
          <span>For n ≥</span><input class="input tiny" value={st.n0 || ''} onInput={(e) => set('n0')(e.currentTarget.value)} aria-label="First value of n" />
          <span>, let P(n) be the predicate that</span>
        </div>
        {kind === 'div' && <div class="row"><span>“</span><input class="input math" style={{ maxWidth: '260px' }} value={st.pe || ''} onInput={(e) => set('pe')(e.currentTarget.value)} placeholder="expression in n" aria-label="Expression" /><span>is divisible by</span><input class="input tiny" value={st.pd || ''} onInput={(e) => set('pd')(e.currentTarget.value)} aria-label="Divisor" /><span>”.</span></div>}
        {kind === 'parity' && <div class="row"><span>“</span><input class="input math" style={{ maxWidth: '260px' }} value={st.pe || ''} onInput={(e) => set('pe')(e.currentTarget.value)} placeholder="expression in n" aria-label="Expression" /><span>is</span><select class="input" style={{ width: 'auto' }} value={st.pp || 'odd'} onChange={(e) => set('pp')(e.currentTarget.value)}><option>odd</option><option>even</option></select><span>”.</span></div>}
        {kind === 'stamps' && <div class="row"><span>“n =</span><input class="input tiny" value={st.pa || ''} onInput={(e) => set('pa')(e.currentTarget.value)} aria-label="First stamp" /><span>x +</span><input class="input tiny" value={st.pb || ''} onInput={(e) => set('pb')(e.currentTarget.value)} aria-label="Second stamp" /><span>y for some integers x, y ≥ 0”.</span></div>}
        {!['div', 'parity', 'stamps'].includes(kind) && <MathField id={`ps-${prob.id}`} kind="alg" syms="alg" value={st.ps || ''} setValue={set('ps')} onEnter={check1} placeholder={prob.sum ? 'e.g. 1·2 + 2·3 + ... + n(n+1) = n(n+1)(n+2)/3   (or S(n) = …)' : prob.seq ? 'e.g. a_n = 25 × 2^(n-1)' : 'e.g. n^2 + 2n - 7 > 0'} />}
        {prob.sum && <div class="small faint">Write the sum with “...”, or use S(n) for it.</div>}
        {!done.p && <div class="step-actions"><Btn kind="primary" onClick={check1}>Check</Btn><Btn kind="ghost" onClick={() => reveal('p', { n0: String(n0), ps: prob.lhs ? `${prob.lhs.replace('a(n+2)', 'a_{n+2}').replace('a(n)', 'a_n')} ${prob.rel} ${prob.rhs}` : '', pe: prob.div?.expr ?? prob.parity?.expr, pd: String(prob.div?.d ?? ''), pp: prob.parity?.odd === false ? 'even' : 'odd', pa: String(prob.stamps?.a ?? ''), pb: String(prob.stamps?.b ?? '') })}>Fill it in</Btn></div>}
        {msgs.p && <Fb kind={msgs.p.kind}>{msgs.p.text}</Fb>}
      </Step>

      <Step n={2} title={strong ? 'Base cases' : 'Base case (B)'} state={stepState('b', done.p)}>
        {strong && <div class="row"><span>How many base cases do you need?</span><input class="input tiny" value={st.nb || ''} onInput={(e) => set('nb')(e.currentTarget.value)} aria-label="Number of base cases" /></div>}
        {(!strong || nbOk(Number(st.nb))) && bases.map((b) => (
          <div key={b.n} class="row" style={{ alignItems: 'center' }}>
            {kind === 'stamps' ? (
              <><span>P({b.n}):  {b.n} = {prob.stamps.a} ×</span><input class="input tiny" value={st['bx' + b.n] || ''} onInput={(e) => set('bx' + b.n)(e.currentTarget.value)} aria-label={`x for ${b.n}`} /><span>+ {prob.stamps.b} ×</span><input class="input tiny" value={st['by' + b.n] || ''} onInput={(e) => set('by' + b.n)(e.currentTarget.value)} aria-label={`y for ${b.n}`} /></>
            ) : kind === 'div' ? (
              <><span>P({b.n}):  <MathText text={showE(prob.div.expr.replace(/n/g, `(${b.n})`))} /> =</span><input class="input mid" value={st['bv' + b.n] || ''} onInput={(e) => set('bv' + b.n)(e.currentTarget.value)} aria-label="Value" /><span>=</span><input class="input tiny" value={st['bq' + b.n] || ''} onInput={(e) => set('bq' + b.n)(e.currentTarget.value)} aria-label="Quotient" /><span>× {prob.div.d}</span></>
            ) : kind === 'parity' ? (
              <><span>P({b.n}):  <MathText text={showE(prob.parity.expr.replace(/n/g, `(${b.n})`))} /> =</span><input class="input mid" value={st['bv' + b.n] || ''} onInput={(e) => set('bv' + b.n)(e.currentTarget.value)} aria-label="Value" /><span>, which is {prob.parity.odd ? 'odd' : 'even'}.</span></>
            ) : (
              <div class="field" style={{ flex: 1 }}><span class="label">P({b.n}) says (substitute n = {b.n})</span>
                <MathField id={`bi-${prob.id}-${b.n}`} kind="alg" syms="alg" value={st['bi' + b.n] || ''} setValue={set('bi' + b.n)} placeholder={prob.base?.find((x) => x.n === b.n)?.inst ? 'numbers only, e.g. ' + prob.base.find((x) => x.n === b.n).simp : 'numbers only'} /></div>
            )}
          </div>
        ))}
        {!done.b && <div class="step-actions"><Btn kind="primary" onClick={check2}>Check</Btn><Btn kind="ghost" onClick={() => {
          const nbFill = strong && nbOk(Number(st.nb)) ? Number(st.nb) : nbWanted;
          const fill = { nb: String(nbFill) };
          for (const b of (kind === 'stamps' ? stampBases(prob) : Array.from({ length: nbFill }, (_, i) => ({ n: n0 + i })))) {
            if (kind === 'stamps') { fill['bx' + b.n] = String(b.x); fill['by' + b.n] = String(b.y); }
            else if (kind === 'div') { const v = evalAt(prob.div.expr, b.n); fill['bv' + b.n] = fmtVal(v); fill['bq' + b.n] = fmtVal(A.div(v, A.Q(prob.div.d))); }
            else if (kind === 'parity') fill['bv' + b.n] = fmtVal(evalAt(prob.parity.expr, b.n));
            else fill['bi' + b.n] = prob.base.find((x) => x.n === b.n)?.inst || '';
          }
          reveal('b', fill);
        }}>Fill it in</Btn></div>}
        {msgs.b && <Fb kind={msgs.b.kind}>{msgs.b.text}</Fb>}
      </Step>

      <Step n={3} title="Inductive hypothesis (R)" state={stepState('h', done.b)}>
        {strong ? (
          <div class="row"><span>Suppose k ≥</span><input class="input tiny" value={st.hk || ''} onInput={(e) => set('hk')(e.currentTarget.value)} aria-label="Lower bound for k" /><span>is such that P({n0}), P({n0 + 1}), …, P(k) are all true.</span></div>
        ) : (
          <>
            <div class="row"><span>Suppose P(k) is true for some k ≥</span><input class="input tiny" value={st.hk || ''} onInput={(e) => set('hk')(e.currentTarget.value)} aria-label="Lower bound for k" /><span>, i.e.</span></div>
            {kind === 'div' ? <div class="row"><input class="input math" style={{ maxWidth: '240px' }} value={st.he || ''} onInput={(e) => set('he')(e.currentTarget.value)} placeholder="expression in k" aria-label="Expression in k" /><span>= {prob.div.d}q for some integer q.</span></div>
              : kind === 'parity' ? <div class="row"><input class="input math" style={{ maxWidth: '240px' }} value={st.he || ''} onInput={(e) => set('he')(e.currentTarget.value)} placeholder="expression in k" aria-label="Expression in k" /><span>is {prob.parity.odd ? 'odd' : 'even'}.</span></div>
                : <MathField id={`hs-${prob.id}`} kind="alg" syms="alg" value={st.hs || ''} setValue={set('hs')} onEnter={check3} placeholder="P(k): the statement with k in place of n" />}
          </>
        )}
        {!done.h && <div class="step-actions"><Btn kind="primary" onClick={check3}>Check</Btn><Btn kind="ghost" onClick={() => reveal('h', { hk: String(kmin), nb: String(st.nb || nbWanted), hs: prob.lhs ? `${prob.lhs.replace('a(n+2)', 'a_{k+2}').replace('a(n)', 'a_k').replace('S(n)', 'S(k)').replace(/n/g, 'k')} ${prob.rel} ${prob.rhs?.replace(/n/g, 'k')}` : '', he: (prob.div?.expr ?? prob.parity?.expr ?? '').replace(/n/g, 'k') })}>Fill it in</Btn></div>}
        {msgs.h && <Fb kind={msgs.h.kind}>{msgs.h.text}</Fb>}
      </Step>

      <Step n={4} title="What you must show: P(k + 1)" state={stepState('g', done.h)}>
        {kind === 'stamps' ? <div>We show P(k + 1) is true, i.e. k + 1 = {prob.stamps.a}x + {prob.stamps.b}y for some integers x, y ≥ 0.</div>
          : kind === 'div' || kind === 'parity' ? <div class="row"><span>We show P(k + 1) is true, i.e.</span><input class="input math" style={{ maxWidth: '260px' }} value={st.ge || ''} onInput={(e) => set('ge')(e.currentTarget.value)} placeholder="the expression with k + 1" aria-label="Expression for k + 1" /><span>{kind === 'div' ? `is divisible by ${prob.div.d}.` : `is ${prob.parity.odd ? 'odd' : 'even'}.`}</span></div>
            : <MathField id={`gs-${prob.id}`} kind="alg" syms="alg" value={st.gs || ''} setValue={set('gs')} onEnter={check4} label="We show P(k + 1) is true, i.e." placeholder="substitute k + 1 for n — mind the brackets" />}
        {!done.g && kind !== 'stamps' && <div class="step-actions"><Btn kind="primary" onClick={check4}>Check</Btn><Btn kind="ghost" onClick={() => reveal('g', { gs: prob.lhs ? `${prob.lhs.replace('a(n+2)', 'a_{k+3}').replace('a(n)', 'a_{k+1}').replace('S(n)', 'S(k+1)').replace(/n/g, '(k+1)')} ${prob.rel} ${prob.rhs?.replace(/n/g, '(k+1)')}` : '', ge: (prob.div?.expr ?? prob.parity?.expr ?? '').replace(/n/g, '(k+1)') })}>Fill it in</Btn></div>}
        {kind === 'stamps' && !done.g && <div class="step-actions"><Btn kind="primary" onClick={() => pass('g')}>Continue</Btn></div>}
        {msgs.g && <Fb kind={msgs.g.kind}>{msgs.g.text}</Fb>}
      </Step>

      <Step n={5} title={kind === 'stamps' ? 'The inductive step' : 'The working'} state={stepState('w', done.g)}>
        {kind === 'stamps' ? (
          <div class="stack-sm">
            <div class="row"><span>k + 1 = (k + 1 −</span><input class="input tiny" value={st.sa || ''} onInput={(e) => set('sa')(e.currentTarget.value)} aria-label="Stamp peeled off" /><span>) + {st.sa || '?'}.</span></div>
            <div class="row"><span>Since k ≥ {kmin}, k + 1 − {st.sa || '?'} ≥</span><input class="input tiny" value={st.sl || ''} onInput={(e) => set('sl')(e.currentTarget.value)} aria-label="Lower bound" /><span>and it is less than k + 1, so P(k + 1 − {st.sa || '?'}) is true by the inductive assumption.</span></div>
            <div class="row"><span>So k + 1 − {st.sa || '?'} = {prob.stamps.a}x + {prob.stamps.b}y, and k + 1 = {prob.stamps.a}(</span><input class="input mid" value={st.sx || ''} onInput={(e) => set('sx')(e.currentTarget.value)} placeholder="in x, y" aria-label="New x" /><span>) + {prob.stamps.b}(</span><input class="input mid" value={st.sy || ''} onInput={(e) => set('sy')(e.currentTarget.value)} placeholder="in x, y" aria-label="New y" /><span>).</span></div>
            {!done.w && <div class="step-actions"><Btn kind="primary" onClick={checkStampStep}>Check</Btn><Btn kind="ghost" onClick={() => reveal('w', { sa: String(prob.stamps.a), sl: String(n0), sx: 'x + 1', sy: 'y' })}>Fill it in</Btn></div>}
          </div>
        ) : (
          <div class="stack-sm">
            <div class="small muted">Start from the left-hand side of P(k + 1) and work line by line to the right-hand side.{prob.div ? ' Write the hypothesis using q, as in P(k).' : ''}{prob.sum ? ' S(k) stands for the sum up to k.' : ''}{prob.seq ? ' Write sequence terms as a_k, a_{k-1}, a_{k+1}.' : ''} Mark the line where you use the inductive hypothesis.</div>
            {chain.map((l, i) => {
              const r = chainRes?.results?.[i];
              return (
                <div key={i} class="pline">
                  <span class="rel">{i === 0 ? '' : (
                    <select class="input" style={{ width: '58px', padding: '4px', fontFamily: 'var(--font-math)', fontSize: '17px' }} value={l.rel || '='} onChange={(e) => { const v = e.currentTarget.value; setChain((C) => C.map((x, j) => (j === i ? { ...x, rel: v } : x))); setChainRes(null); }} aria-label="Relation">{relSyms.map((s) => <option key={s}>{s}</option>)}</select>
                  )}</span>
                  <div class="stack-sm">
                    <input class={cx('input math', r && (r.ok ? 'ok' : 'bad'))} value={l.e} placeholder={i === 0 ? 'left-hand side of P(k + 1)' : 'next expression'} aria-label={`Line ${i + 1}`}
                      onInput={(e) => { const v = e.currentTarget.value; setChain((C) => C.map((x, j) => (j === i ? { ...x, e: v } : x))); setChainRes(null); }}
                      onKeyDown={(e) => { if (e.key === 'Enter') { e.preventDefault(); setChain((C) => (i === C.length - 1 ? [...C, { rel: '=', e: '', why: 'alg' }] : C)); } }} />
                    {l.e && (() => { try { return <div class="preview"><span class="lead">READS AS</span><MathText text={A.pretty(A.parseExpr(l.e))} /></div>; } catch (err) { return <div class="err">{err.message}</div>; } })()}
                    {i > 0 && <select class="input" style={{ width: 'auto', fontSize: '13px', minHeight: '32px', padding: '4px 8px' }} value={l.why || 'alg'} onChange={(e) => { const v = e.currentTarget.value; setChain((C) => C.map((x, j) => (j === i ? { ...x, why: v } : x))); setChainRes(null); }} aria-label="Reason">
                      {Object.entries(REASONS).filter(([k]) => (strong ? k !== 'ih' : k !== 'ihs') && (prob.sum || k !== 'split') && (prob.seq || k !== 'rec')).map(([k, v]) => <option key={k} value={k}>{v}</option>)}
                    </select>}
                    {r && !r.ok && <div class="err">{r.message}</div>}
                  </div>
                  <span class={cx('status', r && (r.ok ? 'ok' : 'bad'))}>{r ? (r.ok ? '✓' : '✗') : ''}</span>
                </div>
              );
            })}
            <div class="symbar">{['^', '×', '(', ')', '√', 'a_{k-1}', 'a_k', 'q', 'S(k)'].filter((s) => (s.startsWith('a_') ? prob.seq : s === 'q' ? prob.div : s === 'S(k)' ? prob.sum : true)).map((s) => <button type="button" key={s} class="sym wide" onMouseDown={(e) => e.preventDefault()} onClick={() => { const el = document.activeElement; if (el && el.tagName === 'INPUT' && el.classList.contains('math')) { const v = el.value, a = el.selectionStart ?? v.length; const nv = v.slice(0, a) + s + v.slice(el.selectionEnd ?? a); el.value = nv; el.dispatchEvent(new Event('input', { bubbles: true })); } }}>{s}</button>)}</div>
            {!done.w && <div class="step-actions">
              <Btn onClick={() => setChain((C) => [...C, { rel: '=', e: '', why: 'alg' }])}>Add line</Btn>
              {chain.length > 1 && <Btn kind="ghost" onClick={() => { setChain((C) => C.slice(0, -1)); setChainRes(null); }}>Remove last line</Btn>}
              <Btn kind="primary" onClick={runChain}>Check working</Btn>
              <Btn kind="ghost" onClick={hintLine}>Show the next line</Btn>
            </div>}
            {chainRes?.overall && <Fb kind={chainRes.overall.ok ? 'good' : 'hint'}>{chainRes.overall.message}</Fb>}
          </div>
        )}
        {msgs.w && kind === 'stamps' && <Fb kind={msgs.w.kind}>{msgs.w.text}</Fb>}
      </Step>

      <Step n={6} title="Conclusion" state={stepState('c', done.w)}>
        <div class="row"><span>So P(k + 1) is true. Hence by</span>
          <select class="input" style={{ width: 'auto' }} value={st.cp || ''} onChange={(e) => set('cp')(e.currentTarget.value)} aria-label="Principle"><option value="">choose…</option><option value="weak">the Principle of Induction</option><option value="strong">the second principle of induction (strong induction)</option></select>
          <span>, P(n) is true for all n ≥</span><input class="input tiny" value={st.cn || ''} onInput={(e) => set('cn')(e.currentTarget.value)} aria-label="All n from" /><span>. □</span></div>
        {!done.c && <div class="step-actions"><Btn kind="primary" onClick={check6}>Check</Btn></div>}
        {msgs.c && <Fb kind={msgs.c.kind}>{msgs.c.text}</Fb>}
      </Step>

      {allDone && (
        <>
          <div class="card stack-sm">
            <div class="h-kicker">How that would have scored (2023 marking pattern)</div>
            {marks.map(([name, k, m]) => <div key={k} class="mark-point"><span class={cx('m status', firstTry[k] ? 'ok' : 'bad')}>{firstTry[k] ? '✓' : '·'}</span><span>{name}{firstTry[k] ? '' : ' (needed help)'}</span><span class="mono">{m}</span></div>)}
            <div class="small muted">The lecturer: “Your answers to induction problems will get around half marks if you get all the steps right except the recursive steps… if your setting out is poor, even if you get the recursive step to work, you may not get much more than half the marks!”</div>
          </div>
          <ModelAnswer lines={modelProof(prob)}>{prob.note && <p class="small muted">{prob.note}</p>}</ModelAnswer>
          <SolvedBanner clean={!S.revealed}>Now try writing the whole thing out in the “Write a full proof” drill.</SolvedBanner>
        </>
      )}
    </div>
  );
}

export function ProofDrill({ preset }) {
  const { prob, pid, setPid, regen } = useProblem(false, preset);
  return (
    <div class="sheet">
      <DrillHeader id="i-proof" kicker="Induction · IND1, IND3" title="Induction proof builder"
        sub="Build the proof in the lecturer’s layout. Every line of algebra is checked exactly over many values of k, so you find mistakes as you make them.">
        <ProblemPicker strong={false} pid={pid} setPid={setPid} regen={regen} />
      </DrillHeader>
      <div class="question"><div class="qmeta"><Chip kind="src">{prob.src}</Chip><Chip kind="marks">5–6 marks</Chip></div><div class="qtext">{prob.ask}</div>
        {prob.seq && <div class="small muted">Sequence: {prob.seq.text}</div>}</div>
      <ProofBuilder prob={prob} drillId="i-proof" />
    </div>
  );
}

export function StrongDrill({ preset }) {
  const { prob, pid, setPid, regen } = useProblem(true, preset);
  const [t, setT] = useState(null);
  const terms = useMemo(() => {
    if (!prob.seq) return null;
    const f = functionsFor(prob).a;
    const start = Math.min(...Object.keys(prob.seq.init).map(Number));
    return Array.from({ length: 5 }, (_, i) => ({ n: start + i, v: A.show(f(A.Q(start + i))) }));
  }, [prob]);
  useEffect(() => setT(null), [prob]);
  return (
    <div class="sheet">
      <DrillHeader id="i-strong" kicker="Induction · IND2, IND3" title="Strong induction"
        sub="Assume all of P(n₀), …, P(k), not just P(k). A recurrence needs one base case per initial value in its definition (IND3); a stamp problem needs as many base cases as the smaller stamp.">
        <ProblemPicker strong pid={pid} setPid={setPid} regen={regen} />
      </DrillHeader>
      <div class="question"><div class="qmeta"><Chip kind="src">{prob.src}</Chip><Chip kind="marks">5–6 marks</Chip></div><div class="qtext">{prob.ask}</div></div>
      {terms && (
        <div class="card stack-sm">
          <div class="label">Warm-up (2024 Q11(a) style): compute the first few terms</div>
          <div class="row">{terms.map((x, i) => <span key={x.n} class="row" style={{ gap: '4px' }}><MathText text={`a_${x.n} =`} /><input class="input tiny" value={t?.[i] ?? ''} onInput={(e) => setT((o) => ({ ...(o || {}), [i]: e.currentTarget.value }))} aria-label={`a ${x.n}`} />{t?.[i] !== undefined && t[i] !== '' && <span class={cx('status', t[i].trim() === x.v ? 'ok' : 'bad')}>{t[i].trim() === x.v ? '✓' : '✗'}</span>}</span>)}</div>
        </div>
      )}
      <ProofBuilder prob={prob} drillId="i-strong" />
    </div>
  );
}

// ---------------------------------------------------------------- spot the flaw
const FLAWS = [
  { title: 'All balls have the same colour', src: 'Tutorial 9 Q5',
    proof: ['Let P(n) be the predicate that any set of n balls all have the same colour, n ≥ 1.', 'Obviously P(1) is true!', 'Assume P(k) is true for some k > 0. Let S = {b₁, b₂, …, b_{k+1}} be a set of k + 1 balls.', 'The subsets {b₁, …, b_k} and {b₂, …, b_{k+1}} each have k elements, so by P(k) the balls in each have the same colour.', 'Clearly then, all balls in their union must have the same colour. So by induction, ∀n ∈ ℕ : P(n).'],
    opts: ['The base case P(1) is false.', 'The step fails when k = 1: the subsets {b₁} and {b₂} don’t overlap, so nothing links their colours.', 'You can’t use P(k) for two different sets.', 'Induction can’t be used for statements about sets.'], a: 1,
    why: 'For k + 1 = 2 the two subsets are {b₁} and {b₂}, with empty intersection, so you can’t conclude they share a colour. The proof shows P(1) and P(k) → P(k + 1) only for k > 1, which is not enough: it must hold for every k ≥ 1.' },
  { title: 'n² + n is odd', src: 'practice',
    proof: ['Let P(n) be the predicate that n² + n is odd, n ≥ 1.', 'Assume P(k): k² + k is odd.', '(k + 1)² + (k + 1) = (k² + k) + 2(k + 1), which is odd + even = odd. So P(k + 1) is true.', 'Hence by induction P(n) is true for all n ≥ 1.'],
    opts: ['The algebra in the step is wrong.', 'There is no base case, and in fact P(1) is false (1 + 1 = 2 is even).', 'Odd + even isn’t always odd.', 'It should use strong induction.'], a: 1,
    why: 'The recursive step is fine, but the base case was skipped, and it fails: 1² + 1 = 2 is even. A correct step on its own proves nothing; in fact n² + n is always even.' },
  { title: 'Every natural number equals the next one', src: 'practice',
    proof: ['Let P(n) be “n = n + 1”.', 'Assume P(k): k = k + 1.', 'Add 1 to both sides: k + 1 = k + 2, which is P(k + 1).', 'So P(n) is true for all n.'],
    opts: ['Adding 1 to both sides isn’t allowed.', 'There is no base case, and P(1) (1 = 2) is false.', 'The hypothesis should be P(k + 1).', 'P(n) isn’t a predicate.'], a: 1,
    why: 'The step P(k) → P(k + 1) is valid, but nothing ever gets the ladder started: P(1) says 1 = 2.' },
  { title: '3c and 5c stamps with one base case', src: 'IND2 warning',
    proof: ['P(n): n = 3x + 5y for some integers x, y ≥ 0, n ≥ 8.', '(B) 8 = 3 + 5, so P(8) is true.', '(R) Suppose P(8), …, P(k) are true, k ≥ 8. Then k + 1 = (k − 2) + 3 and P(k − 2) is true by assumption, so k + 1 = 3(x + 1) + 5y.', 'Hence by strong induction P(n) holds for all n ≥ 8.'],
    opts: ['P(8) is false.', 'For k = 8 and k = 9, k − 2 is 6 or 7, which isn’t covered by the hypothesis: you need base cases 8, 9 and 10.', 'You can’t peel off a 3-cent stamp.', 'Strong induction needs exactly two base cases.'], a: 1,
    why: 'The step only works when k − 2 ≥ 8, i.e. k ≥ 10. So P(9) and P(10) must be base cases too (9 = 3·3, 10 = 5·2), and (R) starts at k ≥ 10. As the notes say, the number of base cases is found by trying the step.' },
  { title: '2ⁿ > n² for all n ≥ 1', src: 'practice',
    proof: ['P(n): 2ⁿ > n², n ≥ 1. (B) 2¹ = 2 > 1 = 1². True.', '(R) Assume 2ᵏ > k². Then 2ᵏ⁺¹ = 2·2ᵏ > 2k² ≥ (k + 1)².', 'So P(k + 1) holds, and by induction 2ⁿ > n² for all n ≥ 1.'],
    opts: ['The base case is wrong.', '2k² ≥ (k + 1)² is only true for k ≥ 3, so the step fails for k = 1 and 2; in fact P(2), P(3) and P(4) are false.', 'You can’t multiply an inequality by 2.', 'It needs the second principle of induction.'], a: 1,
    why: '2k² ≥ (k + 1)² ⇔ k² ≥ 2k + 1, which needs k ≥ 3. And the claim really is false at n = 2 (4 > 4 fails), 3 and 4. The true statement is 2ⁿ ≥ n² for n ≥ 4 (2023 Q9(b)).' },
  { title: 'Assuming what you want to prove', src: 'common mistake',
    proof: ['P(n): 1 + 2 + ⋯ + n = n(n + 1)/2. (B) P(1): 1 = 1. True.', '(R) Assume P(k + 1): 1 + ⋯ + (k + 1) = (k + 1)(k + 2)/2.', 'Then subtracting k + 1 from both sides gives 1 + ⋯ + k = k(k + 1)/2, which is P(k). So P(k + 1) is true.'],
    opts: ['The base case is wrong.', 'It assumes P(k + 1), the thing to be proved, and derives P(k): the logic runs backwards.', 'The subtraction is wrong.', 'It needs two base cases.'], a: 1,
    why: 'The step must start from P(k) and reach P(k + 1). Showing P(k + 1) → P(k) proves nothing.' },
  { title: 'A second-order recurrence with one base case', src: 'IND3 warning',
    proof: ['a₁ = 1, a₂ = 13, aₙ₊₁ = −2aₙ + 3aₙ₋₁ (n > 1). P(n): aₙ = 4 + (−3)ⁿ.', '(B) a₁ = 1 = 4 + (−3)¹. True.', '(R) Suppose P(1), …, P(k) are true, k ≥ 1. Then aₖ₊₁ = −2aₖ + 3aₖ₋₁ = … = 4 + (−3)ᵏ⁺¹.'],
    opts: ['The algebra is wrong.', 'For k = 1 the step uses a₀ and P(0), which don’t exist; it also needs P(2) as a base case and (R) for k ≥ 2.', 'It should use ordinary induction.', 'P(1) is false.'], a: 1,
    why: 'The recurrence only applies for n > 1, and the step uses two previous cases. So check both P(1) and P(2), and run (R) for k ≥ 2, as in the notes.' },
];

export function FlawDrill() {
  const [i, setI] = useState(0);
  const [pick, setPick] = useState(null);
  const S = useSolve('i-flaw', i);
  const f0 = FLAWS[i];
  // shuffle the options (the right one is listed second in the data)
  const order = useMemo(() => new Rng(i * 7919 + 13).shuffle(f0.opts.map((_, j) => j)), [i]);
  const f = { ...f0, opts: order.map((j) => f0.opts[j]), a: order.indexOf(f0.a) };
  useEffect(() => setPick(null), [i]);
  useEffect(() => { if (pick === f.a) S.finish(); }, [pick]);
  return (
    <div class="sheet">
      <DrillHeader id="i-flaw" kicker="Induction" title="Spot the flaw" sub="Each “proof” below proves something false or proves nothing. Find the step that breaks.">
        <Btn onClick={() => setI((x) => (x + FLAWS.length - 1) % FLAWS.length)}>Previous</Btn>
        <Btn onClick={() => setI((x) => (x + 1) % FLAWS.length)}>Next</Btn>
        <span class="small faint">{i + 1} of {FLAWS.length}</span>
      </DrillHeader>
      <div class="question"><div class="qmeta"><Chip kind="src">{f.src}</Chip></div><div class="h3">{f.title}</div>
        <div class="model">{f.proof.map((l, j) => <div key={j} class="model-line"><MathText text={l} /></div>)}</div></div>
      <div class="card stack">
        <div class="label">What is wrong?</div>
        <Options options={f.opts} picked={pick} onPick={setPick} reveal={pick != null} correct={f.a} />
        {pick != null && <Fb kind={pick === f.a ? 'good' : 'bad'}>{f.why}</Fb>}
        {pick != null && <div class="row"><Btn kind="primary" onClick={() => setI((x) => (x + 1) % FLAWS.length)}>Next</Btn></div>}
      </div>
    </div>
  );
}

// ---------------------------------------------------------------- full written proof (Claude-marked)
// The mark split used for written induction proofs (½ predicate, ½–1 base, 1 hypothesis, the rest for the step, ½ conclusion).
// Ordinary proofs follow the split circled on the official 2023 solutions (5 marks: ½ predicate,
// ½ base case, ½ hypothesis, 3 working, ½ conclusion); other totals change the working's share.
// Strong induction (not in 2023) uses the same pattern with 1 mark for the extra base cases.
export function proofScheme(prob, marks) {
  return prob.strong
    ? [{ p: 'Defines P(n) and its domain', m: 0.5 }, { p: 'Checks all the base cases needed', m: 1 }, { p: 'States the strong inductive hypothesis with the right range of k', m: 0.5 }, { p: 'Correct working from the hypothesis to P(k + 1), using the recurrence and P(k), P(k − 1) where marked', m: marks - 2.5 }, { p: 'Concludes with “by strong induction, P(n) for all n ≥ n₀”', m: 0.5 }]
    : [{ p: 'Defines P(n) and its domain', m: 0.5 }, { p: 'Base case checked', m: 0.5 }, { p: 'Inductive hypothesis P(k) stated (and the goal P(k + 1))', m: 0.5 }, { p: 'Correct working from P(k) to P(k + 1), using P(k) where marked', m: marks - 2 }, { p: 'Conclusion: by induction, P(n) for all n ≥ n₀', m: 0.5 }];
}
export const PROOF_NOTES = 'Typed maths may use ^ for powers and * or × for multiplication. Accept any correct algebra, not only the model’s lines. Penalise a missing or false base case, a hypothesis stated for the wrong range, using P(k + 1) in the step, or algebra errors.';
export const PROOF_PLACEHOLDER = 'For n ≥ …, let P(n) be the predicate that “…”.\n(B) P(…) says …, which is true.\n(R) Suppose P(k) is true for some k ≥ …, i.e. …\nWe show P(k + 1) is true, i.e. …\n…\nSo P(k + 1) is true. Hence by induction, P(n) is true for all n ≥ … □';

export function WriteDrill({ preset }) {
  const [pid, setPid] = useState(preset?.ind || 'ineq-2025');
  const prob = BANK.find((p) => p.id === pid) || BANK[0];
  const S = useSolve('i-write', pid);
  const marks = prob.strong ? 6 : prob.id === 'ineq-2025' ? 6 : 5;
  const scheme = proofScheme(prob, marks);
  return (
    <div class="sheet">
      <DrillHeader id="i-write" kicker="Induction" title="Write a full proof"
        sub="Write the proof as you would on paper. Claude marks it against a model answer in the lecturer’s layout, using the mark split circled on the 2023 official solutions (adapted for strong induction); without Claude, use the checklist.">
        <select class="input" style={{ width: 'auto', minWidth: '260px', maxWidth: '100%' }} value={pid} onChange={(e) => setPid(e.currentTarget.value)} aria-label="Problem">
          {[...GROUPS, ...SGROUPS].map(([name, f]) => <optgroup key={name} label={name}>{BANK.filter(f).map((p) => <option key={p.id} value={p.id}>{p.title} · {p.src}</option>)}</optgroup>)}
        </select>
      </DrillHeader>
      <div class="question"><div class="qmeta"><Chip kind="src">{prob.src}</Chip><Chip kind="marks">{marks} marks</Chip></div><div class="qtext">{prob.ask}</div></div>
      <div class="card stack">
        <WrittenAnswer key={pid} id={`write-${pid}`} splitNote={prob.strong ? 'based on the 2023 official solutions, adapted for strong induction' : 'as circled on the 2023 official solutions'} question={prob.ask} marks={marks} model={modelProof(prob).join('\n')} scheme={scheme} rows={12}
          notes={PROOF_NOTES}
          placeholder={PROOF_PLACEHOLDER}
          onScore={(s) => { if (s >= marks - 0.5) S.finish(); }} />
      </div>
    </div>
  );
}
