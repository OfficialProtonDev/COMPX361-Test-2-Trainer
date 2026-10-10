import { useState, useMemo, useEffect } from 'preact/hooks';
import * as G from '../../engines/gram.js';
import * as M from '../../engines/automata.js';
import { Rng } from '../../engines/rng.js';
import { CFG_BANK, CS_BANK, DESIGN, CLASSIFY_POOL, HIER_TF } from '../../data/grambank.js';
import { Automaton, ParseTree } from '../render.jsx';
import {
  MathText, MathOrText, Btn, Seg, Chip, Fb, MathField, Step, Options, DrillHeader, useSolve, useSeed, ModelAnswer, SolvedBanner, cx, Collapse,
} from '../kit.jsx';

const ft = G.formText;
const dkey = (g, target) => `${G.showProductions(g)}|${target}`;

// ---------------------------------------------------------------- shared pieces
export function GrammarBox({ g, label = 'G = (V, T, S, P)' }) {
  const groups = [];
  for (const p of g.P) {
    const l = p.lhs.join('');
    let grp = groups.find((x) => x.l === l);
    if (!grp) groups.push((grp = { l, r: [] }));
    grp.r.push(ft(p.rhs));
  }
  return (
    <div class="panel stack-sm">
      <div class="small muted">{label}, where V = {'{'}<MathText text={g.V.join(', ')} />{'}'}, T = {'{'}{g.T.join(', ')}{'}'}, start symbol <MathText text={g.S} />, and P is:</div>
      <div class="f block" style={{ fontSize: '19px' }}>{groups.map((x) => <div key={x.l}><MathText text={`${x.l} ⇒ ${x.r.join(' | ')}`} /></div>)}</div>
    </div>
  );
}

function prettyState(s) { return s; }

export function EdgeBuilder({ states, alphabet, edges, setEdges, start, accept, last, compareTo }) {
  const [from, setFrom] = useState(states[0]);
  const [lab, setLab] = useState(alphabet[0]);
  const [to, setTo] = useState(states[1] ?? states[0]);
  useEffect(() => { setFrom(states[0]); setTo(states[1] ?? states[0]); setLab(alphabet[0]); }, [states.join(), alphabet.join()]);
  const add = () => { if (!edges.some((e) => e.from === from && e.to === to && e.label === lab)) setEdges([...edges, { from, to, label: lab }]); };
  const merged = M.mergedEdges({ edges });
  let display = merged;
  if (compareTo) {
    const want = new Set(compareTo.map((e) => `${e.from}|${e.label}|${e.to}`));
    const have = new Set(edges.map((e) => `${e.from}|${e.label}|${e.to}`));
    const all = [...edges.map((e) => ({ ...e, cls: want.has(`${e.from}|${e.label}|${e.to}`) ? 'ok' : 'extra' })), ...compareTo.filter((e) => !have.has(`${e.from}|${e.label}|${e.to}`)).map((e) => ({ ...e, cls: 'missing' }))];
    display = [];
    for (const e of all) {
      let x = display.find((y) => y.from === e.from && y.to === e.to && y.cls === e.cls);
      if (!x) display.push((x = { from: e.from, to: e.to, labels: [], cls: e.cls }));
      x.labels.push(e.label);
    }
  }
  return (
    <div class="stack">
      <div class="row eb-controls">
        <label class="field" style={{ width: 'auto' }}><span class="label">From</span>
          <select class="input" value={from} onChange={(e) => setFrom(e.currentTarget.value)}>{states.map((s) => <option key={s}>{s}</option>)}</select></label>
        <label class="field" style={{ width: 'auto' }}><span class="label">Label</span>
          <select class="input" value={lab} onChange={(e) => setLab(e.currentTarget.value)}>{alphabet.map((s) => <option key={s}>{s}</option>)}</select></label>
        <label class="field" style={{ width: 'auto' }}><span class="label">To</span>
          <select class="input" value={to} onChange={(e) => setTo(e.currentTarget.value)}>{states.map((s) => <option key={s}>{s}</option>)}</select></label>
        <div class="field" style={{ width: 'auto' }}><span class="label">&nbsp;</span><Btn kind="primary" onClick={add}>Add edge</Btn></div>
      </div>
      {edges.length > 0 && (
        <div class="row">{edges.map((e, i) => (
          <span key={i} class="chip">
            <MathText text={`${e.from} —${e.label}→ ${e.to}`} />
            <button type="button" class="btn ghost sm" style={{ minHeight: '20px', padding: '0 4px' }} aria-label="Remove edge" onClick={() => setEdges(edges.filter((_, j) => j !== i))}>×</button>
          </span>
        ))}</div>
      )}
      <Automaton states={states} start={start} accept={accept} edges={display} last={last} />
      {compareTo && <div class="small faint">Green: right. Red: not in the construction. Dashed red: missing.</div>}
    </div>
  );
}

// Interactive derivation (click a symbol, choose a production) + typed mode, with a live parse tree.
export function DerivationBuilder({ g, target, onDone, showTree = true, allowTyped = true, initialMode = 'click', onReveal }) {
  const cf = G.isContextFree(g);
  const [mode, setMode] = useState(initialMode);
  const [steps, setSteps] = useState([]); // [{pi, pos, result}]
  const [sel, setSel] = useState(null);
  const [typed, setTyped] = useState('');
  const [msg, setMsg] = useState(null);
  const [typedForms, setTypedForms] = useState(null);
  useEffect(() => { setSteps([]); setSel(null); setTyped(''); setMsg(null); setTypedForms(null); }, [g, target]);
  const forms = [[g.S], ...steps.map((s) => s.result)];
  const cur = forms[forms.length - 1];
  const done = ft(cur) === (target || 'λ') || (target === '' && cur.length === 0);
  useEffect(() => { if (done && steps.length) onDone && onDone(forms); }, [done, steps.length]);
  const opts = useMemo(() => {
    if (sel == null) return [];
    return G.applicable(cur, g).filter((o) => o.pos <= sel && sel < o.pos + g.P[o.pi].lhs.length);
  }, [sel, cur, g]);
  const deadEnd = useMemo(() => {
    if (target == null) return null;
    const t = target;
    const terms = cur.filter((x) => !g.V.includes(x));
    if (terms.length > t.length && cf) return 'There are already more terminals than in the target string.';
    if (cf) {
      let i = 0; while (i < cur.length && !g.V.includes(cur[i])) i++;
      const pre = cur.slice(0, i).join('');
      if (!t.startsWith(pre)) return `The form starts with “${pre}”, but the target doesn’t.`;
      let j = cur.length - 1; while (j >= 0 && !g.V.includes(cur[j])) j--;
      const suf = cur.slice(j + 1).join('');
      if (!t.endsWith(suf)) return `The form ends with “${suf}”, but the target doesn’t.`;
    }
    return null;
  }, [cur, target]);
  const tree = useMemo(() => { try { return cf ? G.treeFromSteps(g, steps) : null; } catch { return null; } }, [steps, g]);
  const apply = (o) => { setSteps((S) => [...S, o]); setSel(null); setMsg(null); };
  const checkTyped = () => {
    const fs = G.parseDerivation(typed, g);
    const r = G.checkDerivation(fs, g, target);
    if (!r.ok) { setMsg({ kind: 'bad', text: r.message }); setTypedForms(null); return; }
    setMsg({ kind: 'good', text: 'Every step applies one production. Correct derivation.' });
    setTypedForms(fs);
    onDone && onDone(fs);
  };
  const showAnswer = () => {
    const d = G.findDerivation(g, target, 250000);
    if (!d) { setMsg({ kind: 'hint', text: 'No derivation found within the search limit.' }); return; }
    onReveal && onReveal();
    if (mode === 'type') setTyped(d.map(ft).join(' ⇒ '));
    else {
      const st = [];
      for (let i = 1; i < d.length; i++) st.push(G.verifyStep(d[i - 1], d[i], g).options[0]);
      setSteps(st);
    }
  };
  const typedTree = useMemo(() => { try { return cf && typedForms ? G.treeFromForms(g, typedForms) : null; } catch { return null; } }, [typedForms]);
  return (
    <div class="stack">
      {allowTyped && <Seg value={mode} onChange={(m) => { setMode(m); setMsg(null); }} label="Input mode" options={[{ value: 'click', label: 'Click to derive' }, { value: 'type', label: 'Type the derivation' }]} />}
      {mode === 'click' ? (
        <>
          <div class="deriv">{forms.map((f, i) => <span key={i}>{i > 0 && <span class="arrow">⇒</span>}<MathText text={ft(f)} upright /></span>)}</div>
          {!done && (
            <div class="panel stack-sm">
              <div class="label">Click a {cf ? 'variable' : 'symbol where a production’s left side starts'} to rewrite it</div>
              <div class="form-line">
                {cur.map((sym, i) => {
                  const isV = g.V.includes(sym);
                  const clickable = cf ? isV : true;
                  return <button type="button" key={i} class={cx('sym-btn', isV && 'var', sel === i && 'sel')} onClick={() => clickable && setSel(i)} disabled={!clickable} style={!cf ? { cursor: 'pointer' } : undefined}>{sym}</button>;
                })}
                {!cur.length && <span class="faint">λ</span>}
              </div>
              {sel != null && (opts.length ? (
                <div class="prod-list">{opts.map((o, k) => {
                  const p = g.P[o.pi];
                  return <button type="button" key={k} class="prod" onClick={() => apply(o)}><MathText text={`${p.lhs.join('')} ⇒ ${ft(p.rhs)}`} />{!cf && <span class="small faint"> at position {o.pos + 1}</span>}</button>;
                })}</div>
              ) : <div class="small faint">No production applies there.</div>)}
            </div>
          )}
          {deadEnd && !done && <Fb kind="hint">{deadEnd} Undo and try another production.</Fb>}
          <div class="step-actions">
            {steps.length > 0 && <Btn kind="ghost" onClick={() => { setSteps((S) => S.slice(0, -1)); setSel(null); }}>Undo</Btn>}
            {steps.length > 0 && <Btn kind="ghost" onClick={() => { setSteps([]); setSel(null); }}>Start again</Btn>}
            {!done && target != null && <Btn kind="ghost" onClick={showAnswer}>Show a derivation</Btn>}
          </div>
          {done && <Fb kind="good">Derived {target || 'λ'} in {steps.length} step{steps.length === 1 ? '' : 's'}.</Fb>}
        </>
      ) : (
        <>
          <MathField id="deriv-typed" kind="gram" syms="gram" value={typed} setValue={setTyped} rows={3} placeholder={`${g.S} ⇒ … ⇒ ${target}`} label="Derivation" hidePreview />
          <div class="step-actions"><Btn kind="primary" onClick={checkTyped}>Check derivation</Btn>{target != null && <Btn kind="ghost" onClick={showAnswer}>Show a derivation</Btn>}</div>
          {msg && <Fb kind={msg.kind}>{msg.text}</Fb>}
        </>
      )}
      {showTree && cf && (mode === 'click' ? steps.length > 0 && tree && <div class="stack-sm"><div class="label">Parse tree so far</div><ParseTree root={tree} isVar={(s) => g.V.includes(s)} /></div>
        : typedTree && <div class="stack-sm"><div class="label">Parse tree</div><ParseTree root={typedTree} isVar={(s) => g.V.includes(s)} /></div>)}
    </div>
  );
}

// ---------------------------------------------------------------- drill: regular grammar → NFSA
export function Reg2NfsaDrill({ preset }) {
  const id = 'g-reg2nfsa';
  const [seed, next] = useSeed(preset?.seed);
  const [src, setSrc] = useState(preset?.gram ? 'paper' : 'random');
  const prob = useMemo(() => {
    const rng = new Rng(seed);
    if (src === 'paper') {
      const pick = preset?.gram && seed === preset.seed ? preset.gram : rng.pick(['t23', 'tut6q3', 'gram2']);
      const texts = { t23: ['S ⇒ 0A | 1B | λ\nA ⇒ 0A | 1B | 1\nB ⇒ 1B | 0A | 0', '2023 Test 2 Q2(a)', '00110'], tut6q3: ['S ⇒ aX | aY | b | c\nX ⇒ bX | a\nY ⇒ cY | b', 'Tutorial 6 Q3', 'abba'], gram2: ['S ⇒ 1A | 0 | λ\nA ⇒ 0A | 1A | 1', 'GRAM2 example', '1101'] };
      const [t, s, w] = texts[pick];
      return { g: G.parseGrammar(t).g, src: s, word: w };
    }
    const g = M.randomRegularGrammar(rng);
    const m = M.grammarToNFSA(g);
    const w = M.sampleAccepted(m, g.T, rng, 3, 6);
    return { g, src: 'random', word: w };
  }, [seed, src, preset]);
  const want = useMemo(() => M.grammarToNFSA(prob.g), [prob]);
  const [edges, setEdges] = useState([]);
  const [msg, setMsg] = useState(null);
  const [compare, setCompare] = useState(false);
  const [part, setPart] = useState(1);
  const S = useSolve(id, seed + src);
  useEffect(() => { setEdges([]); setMsg(null); setCompare(false); setPart(1); }, [prob]);
  const check = () => {
    const r = M.sameEdges(want.edges, edges);
    setCompare(true);
    if (r.same) { setMsg({ kind: 'good', text: 'Exactly the course construction.' }); setPart(2); return; }
    const why = (e) => (e.to === 'Qf' ? (e.label === 'λ' ? `${e.from} ⇒ λ` : `${e.from} ⇒ ${e.label}`) : `${e.from} ⇒ ${e.label}${e.to}`);
    const parts = [];
    if (r.missing.length) parts.push(`Missing: ${r.missing.map((e) => `${e.from} —${e.label}→ ${e.to} (from ${why(e)})`).join('; ')}.`);
    if (r.extra.length) parts.push(`Not needed: ${r.extra.map((e) => `${e.from} —${e.label}→ ${e.to}`).join('; ')}.`);
    setMsg({ kind: 'bad', text: parts.join(' ') });
  };
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Grammars · GRAM2" title="Regular grammar → NFSA"
        sub={<>States are the variables plus one accepting state <MathText text="Q_f" />. <MathText text="A ⇒ aB" /> gives an edge <MathText text="A —a→ B" />; <MathText text="A ⇒ a" /> gives <MathText text="A —a→ Q_f" />; <MathText text="S ⇒ λ" /> gives <MathText text="S —λ→ Q_f" />.</>}>
        <Seg value={src} onChange={(v) => { setSrc(v); next(); }} label="Source" options={[{ value: 'paper', label: 'Past papers & notes' }, { value: 'random', label: 'Random' }]} />
        <Btn onClick={next}>New grammar</Btn>
      </DrillHeader>
      <div class="question">
        <div class="qmeta"><Chip kind="src">{prob.src}</Chip><Chip kind="marks">3 + 2 marks</Chip></div>
        <div class="qtext">Consider the regular grammar below. (a) Draw an NFSA that accepts L(G). (b) Give a derivation and a parse tree for the string <strong class="str">{prob.word}</strong>.</div>
        <GrammarBox g={prob.g} />
      </div>
      <div class="steps">
        <Step n={1} title="(a) Build the NFSA" state={part > 1 ? (S.revealed ? 'revealed' : 'done') : 'active'}>
          <EdgeBuilder states={want.states} alphabet={[...prob.g.T, 'λ']} edges={edges} setEdges={(e) => { setEdges(e); setCompare(false); setMsg(null); }} start={prob.g.S} accept={['Qf']} last={['Qf']} compareTo={compare ? want.edges : null} />
          <div class="step-actions"><Btn kind="primary" onClick={check}>Check NFSA</Btn>
            <Btn kind="ghost" onClick={() => { S.reveal(); setEdges(want.edges); setCompare(true); setMsg({ kind: 'hint', text: 'This is the construction: one edge per production.' }); setPart(2); }}>Show it</Btn></div>
          {msg && <Fb kind={msg.kind}>{msg.text}</Fb>}
        </Step>
        <Step n={2} title={<>(b) Derivation and parse tree for <span class="str">{prob.word}</span></>} state={part < 2 ? 'locked' : S.solved ? 'done' : 'active'}>
          <DerivationBuilder key={dkey(prob.g, prob.word)} g={prob.g} target={prob.word} onDone={() => S.finish()} onReveal={S.reveal} />
          <div class="small faint">Each step of a regular derivation matches one edge of the NFSA: the path for {prob.word} is {M.accepts(want, prob.word) ? 'an accepting path' : ''} through the states you just drew.</div>
        </Step>
      </div>
      {S.solved && <SolvedBanner clean={!S.revealed} onNext={next} />}
    </div>
  );
}

// ---------------------------------------------------------------- drill: DFSA → regular grammar
const T24 = { states: ['q0', 'q1', 'q2'], start: 'q0', accept: ['q2'], edges: [{ from: 'q0', to: 'q0', label: 'a' }, { from: 'q0', to: 'q1', label: 'b' }, { from: 'q1', to: 'q0', label: 'a' }, { from: 'q1', to: 'q2', label: 'b' }, { from: 'q2', to: 'q2', label: 'b' }, { from: 'q2', to: 'q0', label: 'a' }], alphabet: ['a', 'b'] };
const T25 = M.fromDelta(['q0', 'q1', 'q2', 'q3'], ['a', 'b'], { q0: { a: 'q1', b: 'q2' }, q1: { a: 'q1', b: 'q2' }, q2: { a: 'q3', b: 'q2' }, q3: { a: 'q3', b: 'q1' } }, 'q0', ['q3']);
const GRAM2M = { states: ['q0', 'q1', 'q2'], start: 'q0', accept: ['q0', 'q2'], edges: [{ from: 'q0', to: 'q1', label: '0' }, { from: 'q0', to: 'q2', label: '1' }, { from: 'q1', to: 'q1', label: '0' }, { from: 'q1', to: 'q2', label: '1' }, { from: 'q2', to: 'q2', label: '1' }, { from: 'q2', to: 'q1', label: '0' }], alphabet: ['0', '1'] };

export function Fa2RegDrill({ preset }) {
  const id = 'g-fa2reg';
  const [seed, next] = useSeed(preset?.seed);
  const [src, setSrc] = useState(preset?.fa ? 'paper' : 'random');
  const [form, setForm] = useState(preset?.fa === 't25' ? 'table' : 'diagram');
  const prob = useMemo(() => {
    const rng = new Rng(seed);
    if (src === 'paper') {
      const pick = preset?.fa && seed === preset.seed ? preset.fa : rng.pick(['t24', 't25', 'gram2']);
      if (pick === 't24') return { m: T24, src: '2024 Test 2 Q3', word: 'abb', form: 'diagram' };
      if (pick === 't25') return { m: T25, src: '2025 Test 2 Q3', word: 'aabaa', form: 'table' };
      return { m: GRAM2M, src: 'GRAM2 example', word: '010011', form: 'diagram' };
    }
    const { m } = M.randomDFSA(rng);
    return { m: { ...m, alphabet: m.alphabet }, src: 'random', word: M.sampleAccepted(m, m.alphabet, rng, 3, 6), form };
  }, [seed, src, preset, form]);
  const m = prob.m;
  const alphabet = m.alphabet || [...new Set(m.edges.map((e) => e.label))].sort();
  const want = useMemo(() => M.automatonToGrammar(m), [m]);
  const [drawn, setDrawn] = useState([]);
  const [drawMsg, setDrawMsg] = useState(null);
  const [cmp, setCmp] = useState(false);
  const [prods, setProds] = useState({});
  const [pmsg, setPmsg] = useState({});
  const [pOk, setPOk] = useState({});
  const S = useSolve(id, seed + src + form);
  useEffect(() => { setDrawn([]); setDrawMsg(null); setCmp(false); setProds({}); setPmsg({}); setPOk({}); }, [prob]);
  const needDraw = prob.form === 'table';
  const drawDone = !needDraw || drawMsg?.kind === 'good';
  const allOk = m.states.every((q) => pOk[q]);
  const delta = (q, a) => m.edges.find((e) => e.from === q && e.label === a)?.to;
  const checkDraw = () => {
    const r = M.sameEdges(m.edges, drawn);
    setCmp(true);
    setDrawMsg(r.same ? { kind: 'good', text: 'The diagram matches δ.' } : { kind: 'bad', text: `${r.missing.length} edge${r.missing.length === 1 ? '' : 's'} missing, ${r.extra.length} wrong. Each row of the table gives one edge per letter.` });
  };
  const expectedFor = (q) => want.P.filter((p) => p.lhs[0] === q).map((p) => ft(p.rhs));
  const checkProd = (q) => {
    const txt = (prods[q] || '').replace(/^.*?(⇒|=>|->|→)/, '');
    const alts = txt.split('|').filter((x) => x.trim() !== '').map((x) => ft(G.tokenizeForm(x, m.states)));
    const exp = expectedFor(q);
    const missing = exp.filter((x) => !alts.includes(x)), extra = alts.filter((x) => !exp.includes(x));
    if (!missing.length && !extra.length) { setPOk((o) => ({ ...o, [q]: true })); setPmsg((o) => ({ ...o, [q]: null })); return; }
    const reasons = [];
    for (const x of missing) {
      if (x === 'λ') reasons.push(`${q} is the start state and is accepting, so λ ∈ L(M): add ${q} ⇒ λ`);
      else if (x.length === 1) reasons.push(`${q} —${x}→ ${delta(q, x)} goes into an accepting state, so also ${q} ⇒ ${x}`);
      else reasons.push(`the edge ${q} —${x[0]}→ ${x.slice(1)} gives ${q} ⇒ ${x}`);
    }
    for (const x of extra) reasons.push(x === 'λ' ? `${q} ⇒ λ isn’t part of the construction: only the start state gets ⇒ λ, and only when it is accepting` : `${q} ⇒ ${x} doesn’t come from an edge${x.length === 1 ? ' into an accepting state' : ''}`);
    setPmsg((o) => ({ ...o, [q]: reasons.join('; ') + '.' }));
  };
  const [dmsg, setDmsg] = useState(null);
  const [dtext, setDtext] = useState('');
  const checkDeriv = () => {
    const fs = G.parseDerivation(dtext, want);
    const r = G.checkDerivation(fs, want, prob.word);
    if (r.ok) { setDmsg({ kind: 'good', text: `Correct. It follows the path ${M.runDFSA(m, prob.word).path.join(' → ')}.` }); S.finish(); }
    else setDmsg({ kind: 'bad', text: r.message });
  };
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Grammars · GRAM2" title="DFSA → regular grammar"
        sub="V = the states, S = q₀, T = the alphabet. Each edge A —a→ B gives A ⇒ aB, and also A ⇒ a when B is accepting. If q₀ is accepting, add q₀ ⇒ λ.">
        <Seg value={src} onChange={(v) => { setSrc(v); next(); }} label="Source" options={[{ value: 'paper', label: 'Past papers & notes' }, { value: 'random', label: 'Random' }]} />
        {src === 'random' && <Seg value={form} onChange={(v) => setForm(v)} label="Given as" options={[{ value: 'diagram', label: 'Diagram (2024)' }, { value: 'table', label: 'δ table (2025)' }]} />}
        <Btn onClick={next}>New automaton</Btn>
      </DrillHeader>
      <div class="question">
        <div class="qmeta"><Chip kind="src">{prob.src}</Chip><Chip kind="marks">{needDraw ? '5 + 2 marks' : '3 marks'}</Chip></div>
        {needDraw ? (
          <>
            <div class="qtext">Consider the DFSA <MathText text="M = (Q, δ, q0, F)" /> over <MathText text={`X = {${alphabet.join(', ')}}`} /> with <MathText text={`Q = {${m.states.join(', ')}}`} />, <MathText text={`F = {${m.accept.join(', ')}}`} /> and δ as follows. (a) Draw a state diagram for M, then give a regular grammar G which generates L(M). (b) Give a derivation using G for <strong class="str">{prob.word}</strong>.</div>
            <div class="scroll-x"><table class="tt"><thead><tr><th>δ</th>{alphabet.map((a) => <th key={a}>{a}</th>)}</tr></thead>
              <tbody>{m.states.map((q) => <tr key={q}><td class="var"><MathText text={q} /></td>{alphabet.map((a) => <td key={a}><MathText text={delta(q, a)} /></td>)}</tr>)}</tbody></table></div>
          </>
        ) : (
          <>
            <div class="qtext">A DFSA M is drawn below. Give a regular grammar G such that L(G) = L(M), then a derivation for <strong class="str">{prob.word}</strong>.</div>
            <Automaton states={m.states} start={m.start} accept={m.accept} edges={M.mergedEdges(m)} />
          </>
        )}
      </div>
      <div class="steps">
        {needDraw && (
          <Step n={1} title="Draw the state diagram" state={drawDone ? 'done' : 'active'}>
            <EdgeBuilder states={m.states} alphabet={alphabet} edges={drawn} setEdges={(e) => { setDrawn(e); setCmp(false); setDrawMsg(null); }} start={m.start} accept={m.accept} compareTo={cmp ? m.edges : null} />
            <div class="step-actions"><Btn kind="primary" onClick={checkDraw}>Check diagram</Btn><Btn kind="ghost" onClick={() => { S.reveal(); setDrawn(m.edges); setCmp(true); setDrawMsg({ kind: 'good', text: 'Diagram filled in.' }); }}>Show it</Btn></div>
            {drawMsg && <Fb kind={drawMsg.kind}>{drawMsg.text}</Fb>}
          </Step>
        )}
        <Step n={needDraw ? 2 : 1} title="Productions, one state at a time" state={!drawDone ? 'locked' : allOk ? 'done' : 'active'}>
          <div class="small muted">G = (V, T, S, P) with <MathText text={`V = {${m.states.join(', ')}}`} />, <MathText text={`T = {${alphabet.join(', ')}}`} />, <MathText text={`S = ${m.start}`} />. Type the right-hand sides separated by |, e.g. <span class="kbd">a{m.states[1]} | b{m.states[0]}</span>.</div>
          {m.states.map((q) => (
            <div key={q} class="stack-sm">
              <div class="row" style={{ flexWrap: 'nowrap' }}>
                <span class="f" style={{ minWidth: '48px' }}><MathText text={`${q} ⇒`} /></span>
                <input class={cx('input code', pOk[q] && 'ok', pmsg[q] && 'bad')} value={prods[q] || ''} onInput={(e) => setProds((p) => ({ ...p, [q]: e.currentTarget.value }))}
                  onKeyDown={(e) => { if (e.key === 'Enter') checkProd(q); }} placeholder="right-hand sides" disabled={pOk[q]} aria-label={`Productions for ${q}`} />
                {!pOk[q] && <Btn sm kind="ghost" title="Add λ" onClick={() => setProds((p) => ({ ...p, [q]: (p[q] || '').trim() ? (p[q] || '') + ' | λ' : 'λ' }))}>λ</Btn>}
                {!pOk[q] && <Btn sm onClick={() => checkProd(q)}>Check</Btn>}
                {pOk[q] && <span class="status ok">✓</span>}
              </div>
              {pmsg[q] && <div class="err">{pmsg[q]}</div>}
            </div>
          ))}
          <div class="step-actions"><Btn kind="ghost" onClick={() => { S.reveal(); const o = {}; for (const q of m.states) o[q] = expectedFor(q).join(' | '); setProds(o); setPOk(Object.fromEntries(m.states.map((q) => [q, true]))); }}>Show all productions</Btn>
</div>
        </Step>
        <Step n={needDraw ? 3 : 2} title={<>Derivation of <span class="str">{prob.word}</span></>} state={!allOk ? 'locked' : S.solved ? 'done' : 'active'}>
          <MathField id="fa-deriv" kind="gram" syms="gram" value={dtext} setValue={setDtext} rows={2} hidePreview placeholder={`${m.start} ⇒ … ⇒ ${prob.word}`} extraSyms={m.states} />
          <div class="step-actions"><Btn kind="primary" onClick={checkDeriv}>Check</Btn>
            <Btn kind="ghost" onClick={() => { S.reveal(); const d = G.findDerivation(want, prob.word); if (d) setDtext(d.map(ft).join(' ⇒ ')); }}>Show</Btn></div>
          {dmsg && <Fb kind={dmsg.kind}>{dmsg.text}</Fb>}
        </Step>
      </div>
      {S.solved && (
        <>
          <ModelAnswer lines={[`G = (V, T, S, P), where V = {${m.states.join(', ')}}, T = {${alphabet.join(', ')}}, S = ${m.start} and`, `P = {${G.showProductions(want)}}.`]}>
            {prob.src.startsWith('2024') && <Fb kind="hint">The posted 2024 solution writes q₁ ⇒ aq₀ | bq₁ | b. That’s a typo: the b-edge from q₁ goes to q₂, so it should be q₁ ⇒ aq₀ | bq₂ | b.</Fb>}
          </ModelAnswer>
          <SolvedBanner clean={!S.revealed} onNext={next} />
        </>
      )}
    </div>
  );
}

// ---------------------------------------------------------------- drill: derivations & parse trees (CFG)
export function DeriveDrill({ preset }) {
  const id = 'g-derive';
  const [seed, next] = useSeed(preset?.seed);
  const [gid, setGid] = useState(preset?.cfg || 't25q4');
  const bank = CFG_BANK.find((b) => b.id === gid) || CFG_BANK[0];
  const g = useMemo(() => G.parseGrammar(bank.text).g, [bank]);
  const target = useMemo(() => {
    if (preset?.cfg === gid && seed === preset.seed && bank.preset) return bank.preset;
    const rng = new Rng(seed);
    return rng.pick(bank.targets);
  }, [seed, gid]);
  const S = useSolve(id, seed + gid);
  const [descPick, setDescPick] = useState(null);
  const descOpts = useMemo(() => new Rng(seed + 3).shuffle([bank.desc, ...bank.wrong]), [bank, seed]);
  useEffect(() => setDescPick(null), [bank, seed]);
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Grammars · GRAM1, GRAM3" title="Derivations and parse trees"
        sub="One production per ⇒. Any order of rewriting is fine (the notes’ own derivations aren’t always leftmost); the parse tree is drawn as you go.">
        <select class="input" style={{ width: 'auto', minWidth: '220px' }} value={gid} onChange={(e) => setGid(e.currentTarget.value)} aria-label="Grammar">
          {CFG_BANK.map((b) => <option key={b.id} value={b.id}>{b.src}</option>)}
        </select>
        <Btn onClick={next}>Another string</Btn>
      </DrillHeader>
      <div class="question">
        <div class="qmeta"><Chip kind="src">{bank.src}</Chip><Chip kind="marks">3–5 marks</Chip></div>
        <div class="qtext">Give a derivation and a parse tree for the string <strong class="str">{target}</strong>, then describe L(G).</div>
        <GrammarBox g={g} />
      </div>
      <div class="steps">
        <Step n={1} title="Derive the string" state={S.solved ? (S.revealed ? 'revealed' : 'done') : 'active'}>
          <DerivationBuilder key={dkey(g, target)} g={g} target={target} onDone={() => S.finish()} onReveal={S.reveal} />
        </Step>
        <Step n={2} title="Describe L(G)" state={!S.solved ? 'locked' : descPick != null && descOpts[descPick] === bank.desc ? 'done' : 'active'}>
          <Options options={descOpts} picked={descPick} onPick={setDescPick} reveal={descPick != null} correct={descOpts.indexOf(bank.desc)} />
          {descPick != null && <Fb kind={descOpts[descPick] === bank.desc ? 'good' : 'bad'}>{bank.desc}</Fb>}
        </Step>
      </div>
      {S.solved && <SolvedBanner clean={!S.revealed} onNext={next}>In the test, write the derivation on one line and draw the tree with the start symbol at the top.</SolvedBanner>}
    </div>
  );
}

// ---------------------------------------------------------------- drill: context-sensitive derivations
export function CsDrill({ preset }) {
  const id = 'g-cs';
  const [seed, next] = useSeed(preset?.seed);
  const [gid, setGid] = useState(preset?.cs || 'tut6q2');
  const bank = CS_BANK.find((b) => b.id === gid) || CS_BANK[0];
  const g = useMemo(() => G.parseGrammar(bank.text).g, [bank]);
  const target = useMemo(() => (preset?.cs === gid && seed === preset.seed ? bank.preset || bank.targets[0] : new Rng(seed).pick(bank.targets)), [seed, gid]);
  const S = useSolve(id, seed + gid);
  const cls = useMemo(() => G.classify(g), [g]);
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Grammars · GRAM3" title="Derivations in non-context-free grammars"
        sub="Productions can now have more than one symbol on the left. Click the symbol where the left-hand side starts, then pick the production.">
        <select class="input" style={{ width: 'auto', minWidth: '220px' }} value={gid} onChange={(e) => setGid(e.currentTarget.value)} aria-label="Grammar">
          {CS_BANK.map((b) => <option key={b.id} value={b.id}>{b.src}</option>)}
        </select>
        <Btn onClick={next}>Another string</Btn>
      </DrillHeader>
      <div class="question">
        <div class="qmeta"><Chip kind="src">{bank.src}</Chip></div>
        <div class="qtext">Give a derivation for the string <strong class="str">{target}</strong>.</div>
        <GrammarBox g={g} />
      </div>
      <Step n={1} title="Derive it" state={S.solved ? (S.revealed ? 'revealed' : 'done') : 'active'}>
        <DerivationBuilder key={dkey(g, target)} g={g} target={target} onDone={() => S.finish()} onReveal={S.reveal} showTree={false} />
      </Step>
      {S.solved && (
        <>
          <ModelAnswer title="About this grammar"><p>{bank.note}</p><p class="small muted">Type by the course definitions: <strong>{G.TYPE_LABEL[cls.type]}</strong>.</p></ModelAnswer>
          <SolvedBanner clean={!S.revealed} onNext={next} />
        </>
      )}
    </div>
  );
}

// ---------------------------------------------------------------- drill: design a grammar
export function DesignDrill({ preset }) {
  const id = 'g-design';
  const [tid, setTid] = useState(preset?.design || '0n12n');
  const t = DESIGN.find((d) => d.id === tid) || DESIGN[0];
  const [text, setText] = useState('');
  const [res, setRes] = useState(null);
  const S = useSolve(id, tid);
  useEffect(() => { setText(''); setRes(null); }, [tid]);
  const check = () => {
    const r = G.parseGrammar(text);
    if (!r.ok) { setRes({ kind: 'bad', text: r.errors[0] }); return; }
    const c = G.checkDesign(r.g, { alphabet: t.alphabet, test: t.test, maxLen: t.maxLen, requireType: t.req });
    if (c.ok) { setRes({ kind: 'good', text: c.message, warning: c.warning, g: r.g }); S.finish(); }
    else setRes({ kind: 'bad', text: c.message, derivation: c.derivation });
  };
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Grammars · GRAM1–GRAM3" title="Design a grammar"
        sub="Type productions one per line (S ⇒ 0S11 | λ). Your grammar is compared with the language on every string up to a fixed length; if it’s wrong you get the shortest counterexample, with a derivation.">
        <select class="input" style={{ width: 'auto', minWidth: '260px' }} value={tid} onChange={(e) => setTid(e.currentTarget.value)} aria-label="Language">
          {[1, 2, 3].map((l) => <optgroup key={l} label={['', 'Past papers & tutorials', 'Practice', 'Challenge'][l]}>{DESIGN.filter((d) => d.lvl === l).map((d) => <option key={d.id} value={d.id}>{d.title}</option>)}</optgroup>)}
        </select>
      </DrillHeader>
      <div class="question">
        <div class="qmeta"><Chip kind="src">{t.src}</Chip>{t.req && <Chip kind="blue">{t.req} grammar required</Chip>}</div>
        <div class="qtext">Give a {t.req ? `${t.req} ` : ''}grammar that generates <MathOrText text={t.title.replace(/ \(a regular grammar\)$/, '')} />{t.alphabet.length <= 3 ? <> (alphabet <MathText text={`{${t.alphabet.join(', ')}}`} />)</> : ''}.{t.derive ? <> Then give a derivation of <span class="str">{t.derive}</span> using your grammar.</> : ''}</div>
      </div>
      <div class="card stack">
        <MathField id="design-in" kind="gram" syms="gram" value={text} setValue={setText} rows={4} hidePreview label="Productions" placeholder={'S ⇒ …\nA ⇒ …'} />
        <div class="step-actions"><Btn kind="primary" onClick={check}>Check grammar</Btn><Btn kind="ghost" onClick={() => { S.reveal(); setText(t.model); }}>Show a model grammar</Btn></div>
        {res && <Fb kind={res.kind}>{res.text}{res.derivation && <div class="deriv" style={{ marginTop: '6px' }}>{res.derivation.map((f, i) => <span key={i}>{i > 0 && <span class="arrow">⇒</span>}<MathText text={ft(f)} upright /></span>)}</div>}</Fb>}
        {res?.warning && <Fb kind="hint">{res.warning}</Fb>}
        {res?.kind === 'good' && t.derive && <div class="stack-sm"><div class="label">Now derive {t.derive} with your grammar</div><DerivationBuilder key={dkey(res.g, t.derive)} g={res.g} target={t.derive} allowTyped initialMode="type" /></div>}
      </div>
      {(S.solved || S.revealed) && <ModelAnswer lines={t.model.split('\n')}>{t.alt && <p class="small muted">{t.alt}</p>}</ModelAnswer>}
    </div>
  );
}

// ---------------------------------------------------------------- drill: classify / hierarchy
export function ClassifyDrill({ preset }) {
  const id = 'g-classify';
  const [tab, setTab] = useState(preset?.tab || 'classify');
  const [seed, next] = useSeed();
  const item = useMemo(() => new Rng(seed).pick(CLASSIFY_POOL), [seed]);
  const g = useMemo(() => G.parseGrammar(item.text).g, [item]);
  const cls = useMemo(() => G.classify(g), [g]);
  const types = ['regular', 'context-free', 'context-sensitive', 'unrestricted'];
  const [pick, setPick] = useState(null);
  const S = useSolve(id, seed + tab);
  useEffect(() => setPick(null), [seed]);
  const tf = useMemo(() => new Rng(seed).shuffle(HIER_TF).slice(0, 5), [seed]);
  const [ans, setAns] = useState({});
  useEffect(() => setAns({}), [seed]);
  const allAnswered = tf.every((_, i) => ans[i] !== undefined);
  const nRight = tf.filter((q, i) => ans[i] === q.a).length;
  // a round counts as solved with at most one slip, and as clean only when all are right
  useEffect(() => { if (tab === 'tf' && allAnswered && nRight >= tf.length - 1) S.finish(nRight === tf.length); }, [allAnswered, tab]);
  useEffect(() => { if (tab === 'classify' && pick != null && types[pick] === cls.type) S.finish(); }, [pick]);
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Grammars · GRAM2–GRAM4" title="Grammar types and the Chomsky hierarchy"
        sub="regular ⊂ context-free ⊂ context-sensitive ⊂ arbitrary. Name the most restrictive type each grammar satisfies, using the exact definitions from the notes.">
        <Seg value={tab} onChange={(v) => { setTab(v); next(); }} label="Exercise" options={[{ value: 'classify', label: 'Classify a grammar' }, { value: 'tf', label: 'True / false (2023 Q4, 2024 Q9)' }]} />
        <Btn onClick={next}>New question</Btn>
      </DrillHeader>
      {tab === 'classify' ? (
        <>
          <div class="question"><div class="qmeta"><Chip kind="src">{item.src}</Chip></div><div class="qtext">What is the most restrictive type of this grammar?</div><GrammarBox g={g} /></div>
          <div class="card stack">
            <Options options={types.map((t) => G.TYPE_LABEL[t])} picked={pick} onPick={setPick} reveal={pick != null} correct={types.indexOf(cls.type)} />
            {pick != null && (
              <Fb kind={types[pick] === cls.type ? 'good' : 'bad'}>
                <div class="stack-sm">
                  <div><strong>{G.TYPE_LABEL[cls.type]}.</strong></div>
                  {cls.why.regular.length > 0 && <div>Not regular: {cls.why.regular.slice(0, 3).join('; ')}.</div>}
                  {cls.type !== 'regular' && cls.why.cf.length > 0 && <div>Not context-free: {cls.why.cf.slice(0, 3).join('; ')}.</div>}
                  {cls.why.cs.length > 0 && <div>Not context-sensitive: {cls.why.cs.slice(0, 3).join('; ')}.</div>}
                </div>
              </Fb>
            )}
            {pick != null && <SolvedBanner clean={types[pick] === cls.type} missed={types[pick] !== cls.type} onNext={next} />}
          </div>
        </>
      ) : (
        <div class="card stack">
          {tf.map((q, i) => (
            <div key={i} class="stack-sm" style={{ paddingBottom: '10px', borderBottom: '1px dashed var(--rule)' }}>
              <div class="row"><span>{q.s}</span><span class="spacer" /><Chip kind="src">{q.src}</Chip></div>
              <div class="row">
                {[true, false].map((v) => <Btn key={String(v)} sm kind={ans[i] === v ? (v === q.a ? 'primary' : 'danger') : ''} onClick={() => ans[i] === undefined && setAns((a) => ({ ...a, [i]: v }))}>{v ? 'True' : 'False'}</Btn>)}
                {ans[i] !== undefined && <span class={cx('chip', ans[i] === q.a ? 'good' : 'bad')}>{ans[i] === q.a ? 'Right' : `No: ${q.a ? 'true' : 'false'}`}</span>}
              </div>
              {ans[i] !== undefined && <div class="small muted">{q.why}</div>}
            </div>
          ))}
          {allAnswered && <SolvedBanner clean={nRight === tf.length} missed={nRight < tf.length - 1} onNext={next}>{nRight} / {tf.length} right.</SolvedBanner>}
          <Collapse title="Grammar types and automata (GRAM4 table)">
            <table class="plain"><thead><tr><th>Grammar type</th><th>Automaton</th><th>Language class</th></tr></thead>
              <tbody><tr><td>Regular (type 3)</td><td>DFSA</td><td>regular</td></tr><tr><td>Context-free (type 2)</td><td>Pushdown automaton</td><td>context-free</td></tr><tr><td>Context-sensitive (type 1)</td><td>Linear bounded automaton</td><td>context-sensitive (all recursive)</td></tr><tr><td>Arbitrary (type 0)</td><td>Turing machine (semidecides)</td><td>recursively enumerable</td></tr></tbody></table>
          </Collapse>
        </div>
      )}
    </div>
  );
}
