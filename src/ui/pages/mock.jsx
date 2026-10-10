// Timed mock tests: a fresh 40-mark paper in the shape of a past Test 2, answered without
// feedback, then marked: auto-marked parts at once, written parts by Claude (or a checklist).
import { useState, useEffect, useMemo, useRef } from 'preact/hooks';
import { Rng, newSeed } from '../../engines/rng.js';
import * as TM from '../../engines/tmcode.js';
import * as G from '../../engines/gram.js';
import * as M from '../../engines/automata.js';
import * as P from '../../engines/prop.js';
import * as A from '../../engines/algebra.js';
import { parsePred, tryParsePred, showPred, comparePred, pushAll, describeWorld } from '../../engines/pred.js';
import { checkRestricted, solutionSteps, OPNAME } from '../../engines/nand.js';
import { FORMS, THEMES, makeArgument, falsify } from '../../engines/argue.js';
import { BANK, generated, modelProof, functionsFor } from '../../engines/induction.js';
import { THEORY } from '../../data/theory.js';
import { CFG_BANK, DESIGN, HIER_TF } from '../../data/grambank.js';
import { STATUS_BANK, NAND_BANK, DNF_SPECIAL } from '../../data/propbank.js';
import { SCENARIOS, sentences } from '../../data/predbank.js';
import { Automaton, ParseTree, NTMDiagram } from '../render.jsx';
import { MathText, MathOrText, Btn, Seg, Chip, Fb, MathField, Options, Collapse, TF, cx } from '../kit.jsx';
import { askMark, getSample } from '../marking.jsx';
import { CodeTable, SymbolEntry } from '../drills/tm.jsx';
import { GrammarBox, EdgeBuilder } from '../drills/gram.jsx';
import { genWff, TruthTable, LawSheet } from '../drills/prop.jsx';
import { disguise } from '../drills/pred.jsx';
import { proofScheme, PROOF_NOTES, PROOF_PLACEHOLDER } from '../drills/ind.jsx';
import { upsertMock, mocks } from '../store.js';
import { DRILLS } from '../registry.jsx';
import { CLAUDE_URL } from '../host.js';

const MOCK_KEY = 'compx361-t2-mock-v1';
const DURATION = 60 * 60 * 1000;

function loadMock() { try { const r = window.localStorage.getItem(MOCK_KEY); return r ? JSON.parse(r) : null; } catch { return null; } }
function saveMock(s) { try { if (s) window.localStorage.setItem(MOCK_KEY, JSON.stringify(s)); else window.localStorage.removeItem(MOCK_KEY); } catch { /* storage unavailable */ } }
// For the overview: a mock test started in this browser and not yet submitted (null if none).
export function activeMock(now = Date.now()) {
  const s = loadMock();
  if (!s || s.v !== 1 || !s.seed || !SHAPES[s.shape] || s.submittedAt) return null;
  const left = s.startedAt + DURATION - now;
  return { timed: !!s.timed, left, over: !!s.timed && left <= 0 };
}

// ---------------------------------------------------------------- helpers
const half = (x) => Math.max(0, Math.floor(x * 2 + 1e-9) / 2);
const fmt = (x) => (Number.isInteger(x) ? String(x) : String(Math.round(x * 2) / 2));
const ft = G.formText;
const SUBD = '₀₁₂₃₄₅₆₇₈₉';
const subs = (t) => String(t ?? '').replace(/q(\d+)/g, (_, n) => 'q' + [...n].map((c) => SUBD[c]).join(''));
const subn = (n) => [...String(n)].map((c) => SUBD[c] ?? c).join('');
const norm = (s) => (s || '').replace(/[₀-₉]/g, (d) => String(d.charCodeAt(0) - 0x2080));
const ROMAN = ['i', 'ii', 'iii', 'iv', 'v'];
const LETTERS = 'abcdefgh';
const Str = ({ children }) => <span class="str">{children}</span>;

function answered(a) {
  if (!a) return false;
  return Object.values(a).some((v) => {
    if (v == null || v === '') return false;
    if (Array.isArray(v)) return v.length > 0;
    if (typeof v === 'object') return Object.values(v).some((x) => x !== '' && x != null);
    if (typeof v === 'string') return v.trim() !== '';
    return true;
  });
}

function Part({ label, marks, children }) {
  return (
    <div class="mpart">
      <div class="mpart-head"><span class="mpart-label">{label}</span>{marks != null && <span class="mpart-marks">[{fmt(marks)}]</span>}</div>
      {children}
    </div>
  );
}

function WrittenBox({ id, value, set, rows = 6, placeholder }) {
  return <textarea id={id} class="input" rows={rows} value={value || ''} placeholder={placeholder} spellcheck={true} onInput={(e) => set(e.currentTarget.value)} aria-label="Your answer" />;
}

function DeltaTable({ m, alphabet }) {
  const delta = (q, x) => m.edges.find((e) => e.from === q && e.label === x)?.to;
  return (
    <div class="scroll-x"><table class="tt"><thead><tr><th>δ</th>{alphabet.map((a) => <th key={a}>{a}</th>)}</tr></thead>
      <tbody>{m.states.map((q) => <tr key={q}><td class="var"><MathText text={q} /></td>{alphabet.map((a) => <td key={a}><MathText text={delta(q, a)} /></td>)}</tr>)}</tbody></table></div>
  );
}

function DerivField({ id, value, set, g, word, extra }) {
  return <MathField id={id} kind="gram" syms="gram" extraSyms={extra} value={value || ''} setValue={(v) => set(typeof v === 'function' ? v(value || '') : v)} rows={2} hidePreview placeholder={`${g.S} ⇒ … ⇒ ${word}`} />;
}

function gradeDeriv(text, grammars, word) {
  if (!text || !text.trim()) return { ok: false, note: 'No answer.' };
  let first = null;
  for (const g of grammars) {
    if (!g) continue;
    const r = G.checkDerivation(G.parseDerivation(norm(text), g), g, word);
    if (r.ok) return { ok: true, note: 'A correct derivation: every step applies one production.' };
    if (!first) first = r.message;
  }
  return { ok: false, note: first };
}

const prText = (p) => `${p.lhs.join('')} ⇒ ${ft(p.rhs)}`;
const sortStates = (xs) => [...xs].sort((a, b) => Number(a.slice(1)) - Number(b.slice(1)));

// ---------------------------------------------------------------- question kinds
// Each kind: gen(rng, opt, marks, ctx) → data; Q({d, a, set, locked, n}); auto(d, a) → [{label, got, max, note}];
// written(d, a) → [{key, label, question, marks, model, scheme, notes, answer}]; self(d, a) → [{key, label, marks}];
// Review({d, a}) shows the model answer; drill(d) → {id, preset}; topic.
export const KINDS = {};

// ---- Turing number, first 60 bits
const normSym = (c) => ({ x: '⊥', X: '⊥', u: '⊥', U: '⊥', _: '⊥', B: 'b', l: 'L', r: 'R' }[c] || c);
const listForm = (syms) => syms.join('').replace(/,/g, ', ');
const tmEdges = (dec) => dec.instructions.filter((i) => !i.unknown && !i.undefined && !i.error && i.to != null).map((i) => ({ from: i.state, read: i.read, to: i.to, act: i.act }));
const mergeTM = (edges) => {
  const out = [];
  for (const e of edges) {
    let x = out.find((y) => y.from === e.from && y.to === e.to);
    if (!x) out.push((x = { from: e.from, to: e.to, labels: [] }));
    x.labels.push(`${e.read}/${e.act}`);
  }
  return out;
};

function TMEdgeEntry({ edges, setEdges, N }) {
  const [f, setF] = useState('0');
  const [r, setR] = useState('0');
  const [act, setAct] = useState('R');
  const [to, setTo] = useState('1');
  const add = () => {
    if (f === '' || to === '') return;
    const e = { from: Number(f), read: r, to: Number(to), act };
    setEdges([...edges.filter((x) => !(x.from === e.from && x.read === e.read)), e]);
  };
  const states = [...new Set([0, ...(N != null ? [N] : []), ...edges.flatMap((e) => [e.from, e.to])])].sort((x, y) => x - y);
  return (
    <div class="stack">
      <div class="row eb-controls">
        <label class="field" style={{ width: 'auto' }}><span class="label">From state</span><input class="input tiny" inputMode="numeric" value={f} onInput={(e) => setF(e.currentTarget.value.replace(/\D/g, ''))} /></label>
        <label class="field" style={{ width: 'auto' }}><span class="label">Reading</span><select class="input" value={r} onChange={(e) => setR(e.currentTarget.value)}>{TM.READS.map((x) => <option key={x}>{x}</option>)}</select></label>
        <label class="field" style={{ width: 'auto' }}><span class="label">Action</span><select class="input" value={act} onChange={(e) => setAct(e.currentTarget.value)}>{TM.ACTIONS.map((x) => <option key={x}>{x}</option>)}</select></label>
        <label class="field" style={{ width: 'auto' }}><span class="label">To state</span><input class="input tiny" inputMode="numeric" value={to} onInput={(e) => setTo(e.currentTarget.value.replace(/\D/g, ''))} /></label>
        <div class="field" style={{ width: 'auto' }}><span class="label">&nbsp;</span><Btn kind="primary" onClick={add}>Add edge</Btn></div>
      </div>
      {edges.length > 0 && (
        <div class="row">{edges.map((e, i) => (
          <span key={i} class="chip"><MathText text={`${e.from} —${e.read}/${e.act}→ ${e.to}`} />
            <button type="button" class="btn ghost sm" style={{ minHeight: '20px', padding: '0 4px' }} aria-label="Remove edge" onClick={() => setEdges(edges.filter((_, j) => j !== i))}>×</button></span>
        ))}</div>
      )}
      {N != null ? <NTMDiagram N={N} states={states} edges={mergeTM(edges)} title="Your NTM" /> : <div class="small faint">Enter the halt state to see your diagram.</div>}
    </div>
  );
}

KINDS.tm60 = {
  topic: 'Turing machines',
  drill: () => ({ id: 'tm-decode' }),
  gen(rng) {
    for (let t = 0; t < 80; t++) {
      const ntm = TM.randomNTM(rng, { N: rng.pick([2, 3, 3, 4, 5, 10, 11, 12]), fill: 0.7 });
      const bits = TM.first60(ntm);
      const dec = TM.decode(bits, { partial: true });
      const edges = tmEdges(dec);
      if (!dec.errors.length && edges.length >= 2) return { bits, dec, edges };
    }
    const bits = '100111111110001111101000111111100011111011101111111101111111';
    const dec = TM.decode(bits, { partial: true });
    return { bits, dec, edges: tmEdges(dec) };
  },
  Q({ d, a, set, n }) {
    const blocks = TM.blocksOf(d.bits);
    return (
      <>
        <div class="qtext">The first 60 bits of the Turing number in binary of an NTM (normalised Turing machine) are as follows. Using the table, draw as much as you can of the NTM, including the halt state.</div>
        <Collapse title="Code table (supplied in the test)"><CodeTable /></Collapse>
        <Part label="Convert the bits using the table (one symbol per block)" marks={1.5}>
          <SymbolEntry blocks={blocks} value={a.syms || ''} setValue={(v) => set('syms', v)} />
        </Part>
        <Part label="Draw the NTM: its halt state and every edge the bits determine" marks={2.5}>
          <div class="row"><label class="row" for={`m${n}-N`}>Halt state N =</label><input id={`m${n}-N`} class="input tiny" inputMode="numeric" value={a.N || ''} onInput={(e) => set('N', e.currentTarget.value.replace(/\D/g, ''))} /></div>
          <TMEdgeEntry edges={a.edges || []} setEdges={(e) => set('edges', e)} N={a.N !== undefined && a.N !== '' ? Number(a.N) : null} />
        </Part>
      </>
    );
  },
  auto(d, a) {
    const want = d.dec.symbols;
    const got = [...(a.syms || '').replace(/\s+/g, '')].map(normSym);
    let wrong = Math.abs(want.length - got.length);
    for (let i = 0; i < Math.min(want.length, got.length); i++) if (want[i] !== got[i]) wrong++;
    const sym = !got.length ? 0 : wrong === 0 ? 1.5 : wrong <= 2 ? 1 : wrong <= 4 ? 0.5 : 0;
    const nOk = String(a.N ?? '').trim() !== '' && Number(a.N) === d.dec.N;
    const key = (e) => `${e.from}|${e.read}|${e.to}|${e.act}`;
    const W = new Set(d.edges.map(key));
    const U = (a.edges || []).map(key);
    const right = U.filter((k) => W.has(k)).length, extra = U.length - right;
    return [
      { label: 'Converting the bits', got: sym, max: 1.5, note: !got.length ? 'No answer.' : wrong ? `${wrong} symbol${wrong === 1 ? '' : 's'} wrong or missing. It reads ${listForm(want)}` : `Right: ${listForm(want)}` },
      { label: 'Halt state', got: nOk ? 0.5 : 0, max: 0.5, note: nOk ? `N = ${d.dec.N}.` : `N = ${d.dec.N}: the number before the first “/” (several digits make one number).` },
      { label: 'Edges', got: half((2 * Math.max(0, right - extra)) / W.size), max: 2, note: `${right} of the ${W.size} edges right${extra ? `, ${extra} wrong` : ''}. Instructions go 3 per state, reading 0, 1, b in that order; ⊥ means no edge.` },
    ];
  },
  Review({ d }) {
    const edges = TM.edgesOf(d.dec.delta);
    const known = [...new Set([0, d.dec.N, ...edges.flatMap((e) => [e.from, e.to])])].sort((x, y) => x - y);
    return (
      <div class="stack-sm">
        <div class="model-line"><MathText text={`The bits convert to:  ${listForm(d.dec.symbols)}`} /></div>
        <NTMDiagram N={d.dec.N} states={known} edges={edges} />
        <div class="small muted">Start state 0, halt state {d.dec.N} (double circle). Edge labels are “read/action”. The instructions after the cut-off are unknown.</div>
      </div>
    );
  },
};

// ---- written theory answers
const EXTRA_THEORY = {
  undecidableCFG: {
    id: 'undecidableCFG', title: 'Undecidable problem about CFGs', marks: 1,
    q: 'Give one example of an undecidable problem involving context-free grammars.',
    model: 'Deciding whether two context-free grammars generate the same language: is L(G₁) = L(G₂)?\n(Others: is L(G₁) ⊆ L(G₂)? Is L(G₁) ∩ L(G₂) empty? Does G generate every string over its alphabet?)',
    scheme: [{ p: 'A correct undecidable problem about context-free grammars', m: 1 }],
    notes: 'Accept: L(G₁) = L(G₂); L(G₁) ⊆ L(G₂); L(G₁) ∩ L(G₂) = ∅; whether a CFG generates every string. Do not accept decidable problems, such as whether a given string is in L(G) or whether L(G) is empty.',
  },
};
KINDS.theory = {
  topic: 'Turing machines',
  drill: (d) => ({ id: 'tm-theory', preset: { theory: d.t.id === 'undecidableCFG' ? 'undecidable' : d.t.id } }),
  gen(rng, opt) { const id = rng.pick(opt.ids); return { t: THEORY.find((x) => x.id === id) || EXTRA_THEORY[id] }; },
  Q({ d, a, set, n }) {
    return (
      <>
        <div class="qtext">{d.t.q}</div>
        <WrittenBox id={`m${n}-w`} value={a.text} set={(v) => set('text', v)} rows={d.marks >= 3 ? 6 : 3} placeholder="Write your answer in sentences." />
      </>
    );
  },
  written(d, a) { return [{ key: 'w', label: d.t.title, question: d.t.q, marks: d.marks, model: d.t.model, scheme: d.t.scheme, notes: d.t.notes, answer: a.text || '' }]; },
};

// ---- DFSA → regular grammar
const T25 = M.fromDelta(['q0', 'q1', 'q2', 'q3'], ['a', 'b'], { q0: { a: 'q1', b: 'q2' }, q1: { a: 'q1', b: 'q2' }, q2: { a: 'q3', b: 'q2' }, q3: { a: 'q3', b: 'q1' } }, 'q0', ['q3']);

function sameLanguage(g, m, maxLen) {
  const L = G.language(g, maxLen);
  for (const w of G.allStrings(m.alphabet, maxLen)) if (L.has(w) !== M.accepts(m, w)) return false;
  return true;
}
function gradeGrammar(m, want, text) {
  if (!text || !text.trim()) return { frac: 0, note: 'No answer.' };
  const r = G.parseGrammar(norm(text), { V: m.states, S: m.start });
  if (!r.ok) return { frac: 0, note: r.errors[0] };
  const W = want.P.map(prText), H = r.g.P.map(prText);
  const right = H.filter((x) => W.includes(x)).length, extra = H.length - right;
  if (right === W.length && !extra) return { frac: 1, note: 'Exactly the course construction.', g: r.g };
  if (G.classify(r.g).type === 'regular' && sameLanguage(r.g, m, 7)) return { frac: 1, note: 'Not the standard construction, but a regular grammar for exactly L(M).', g: r.g };
  const missing = W.filter((x) => !H.includes(x)), extras = H.filter((x) => !W.includes(x));
  const why = [];
  if (missing.length) why.push(`Missing: ${missing.map(subs).join(', ')}.`);
  if (extras.length) why.push(`Not from M: ${extras.map(subs).join(', ')}.`);
  return { frac: Math.max(0, right - extra) / W.length, note: why.join(' '), g: r.g };
}

KINDS.fa2reg = {
  topic: 'Grammars & automata',
  drill: () => ({ id: 'g-fa2reg' }),
  gen(rng, opt) {
    let m;
    try { m = M.randomDFSA(rng).m; } catch { m = T25; }
    const word = M.sampleAccepted(m, m.alphabet, rng, 4, 6) || M.sampleAccepted(m, m.alphabet, rng, 1, 8);
    return { m, word, form: opt.form, g: M.automatonToGrammar(m) };
  },
  Q({ d, a, set, n }) {
    const { m } = d;
    const gramField = (
      <MathField id={`m${n}-g`} kind="gram" syms="gram" extraSyms={m.states} rows={4} hidePreview value={a.gram || ''} setValue={(v) => set('gram', typeof v === 'function' ? v(a.gram || '') : v)}
 label="P (one production line per state; V is the set of states and S = q0)" placeholder={`${m.states[0]} ⇒ …\n${m.states[1]} ⇒ …`} />
    );
    if (d.form === 'table') {
      return (
        <>
          <div class="qtext">Consider the DFSA <MathText text="M = (Q, δ, q0, F)" /> over <MathText text={`X = {${m.alphabet.join(', ')}}`} />, with <MathText text={`Q = {${m.states.join(', ')}}`} />, <MathText text={`F = {${sortStates(m.accept).join(', ')}}`} /> and <MathText text="δ" /> given by the table.</div>
          <DeltaTable m={m} alphabet={m.alphabet} />
          <Part label="(a) Draw a state diagram for M," marks={2}>
            <EdgeBuilder states={m.states} alphabet={m.alphabet} edges={a.drawn || []} setEdges={(e) => set('drawn', e)} start={m.start} accept={m.accept} />
          </Part>
          <Part label="and then give a regular grammar G = (V, T, S, P) which generates L(M)." marks={3}>{gramField}</Part>
          <Part label={<>(b) The string <Str>{d.word}</Str> is accepted by M. Give a derivation using G for this string.</>} marks={2}>
            <DerivField id={`m${n}-d`} value={a.deriv} set={(v) => set('deriv', v)} g={d.g} word={d.word} extra={m.states} />
          </Part>
        </>
      );
    }
    return (
      <>
        <div class="qtext">A DFSA M is drawn below. Give a regular grammar G which is such that L(G) = L(M).</div>
        <Automaton states={m.states} start={m.start} accept={m.accept} edges={M.mergedEdges(m)} />
        <Part label="G = (V, T, S, P), where" marks={3}>{gramField}</Part>
      </>
    );
  },
  auto(d, a) {
    const out = [];
    const gmax = 3;
    if (d.form === 'table') {
      const r = M.sameEdges(d.m.edges, a.drawn || []);
      const errs = r.missing.length + r.extra.length;
      out.push({ label: 'State diagram', got: !(a.drawn || []).length ? 0 : errs === 0 ? 2 : errs <= 2 ? 1 : 0, max: 2, note: !(a.drawn || []).length ? 'No answer.' : errs ? `${r.missing.length} edge${r.missing.length === 1 ? '' : 's'} missing, ${r.extra.length} wrong.` : 'Matches δ exactly.' });
    }
    const gm = gradeGrammar(d.m, d.g, a.gram);
    out.push({ label: 'Regular grammar', got: half(gmax * gm.frac), max: gmax, note: gm.note });
    if (d.form === 'table') {
      const dv = gradeDeriv(a.deriv, [gm.g, d.g], d.word);
      out.push({ label: <>Derivation of <Str>{d.word}</Str></>, got: dv.ok ? 2 : 0, max: 2, note: dv.note });
    }
    return out;
  },
  Review({ d }) {
    const deriv = d.form === 'table' ? G.findDerivation(d.g, d.word) : null;
    return (
      <div class="stack-sm">
        {d.form === 'table' && <Automaton states={d.m.states} start={d.m.start} accept={d.m.accept} edges={M.mergedEdges(d.m)} />}
        <div class="model-line"><MathText text={`G = (V, T, S, P), where V = {${d.m.states.join(', ')}}, the start variable S = q0, T = {${d.m.alphabet.join(', ')}} and`} /></div>
        <div class="model-line"><MathText text={`P = {${G.showProductions(d.g)}}.`} /></div>
        {deriv && <div class="model-line"><MathText text={`(b) ${deriv.map(ft).join(' ⇒ ')}.`} /></div>}
        <div class="small muted">Each edge A —a→ B gives A ⇒ aB, plus A ⇒ a when B is accepting{d.m.accept.includes(d.m.start) ? '; q₀ is accepting, so also q₀ ⇒ λ' : ''}.</div>
      </div>
    );
  },
};

// ---- regular grammar → NFSA
KINDS.reg2nfsa = {
  topic: 'Grammars & automata',
  drill: () => ({ id: 'g-reg2nfsa' }),
  gen(rng) {
    const g = M.randomRegularGrammar(rng);
    const nfa = M.grammarToNFSA(g);
    const word = M.sampleAccepted(nfa, g.T, rng, 4, 6) || M.sampleAccepted(nfa, g.T, rng, 1, 8);
    return { g, nfa, word };
  },
  Q({ d, a, set, n }) {
    return (
      <>
        <div class="qtext">Consider the regular grammar G below.</div>
        <GrammarBox g={d.g} />
        <Part label="(a) Draw an NFSA that accepts the strings in L(G)." marks={3}>
          <EdgeBuilder states={d.nfa.states} alphabet={[...d.g.T, 'λ']} edges={a.edges || []} setEdges={(e) => set('edges', e)} start={d.g.S} accept={['Qf']} last={['Qf']} />
        </Part>
        <Part label={<>(b) Give a derivation and a parse tree for the string <Str>{d.word}</Str>.</>} marks={2}>
          <DerivField id={`m${n}-d`} value={a.deriv} set={(v) => set('deriv', v)} g={d.g} word={d.word} extra={d.g.V} />
          <div class="small faint">Draw the parse tree on paper: after you submit, you compare it with the model tree.</div>
        </Part>
      </>
    );
  },
  auto(d, a) {
    const r = M.sameEdges(d.nfa.edges, a.edges || []);
    const right = d.nfa.edges.length - r.missing.length;
    const dv = gradeDeriv(a.deriv, [d.g], d.word);
    return [
      { label: 'NFSA', got: half((3 * Math.max(0, right - r.extra.length)) / d.nfa.edges.length), max: 3, note: !(a.edges || []).length ? 'No answer.' : r.same ? 'Exactly the course construction.' : `${r.missing.length} edge${r.missing.length === 1 ? '' : 's'} missing, ${r.extra.length} wrong.` },
      { label: <>Derivation of <Str>{d.word}</Str></>, got: dv.ok ? 1.5 : 0, max: 1.5, note: dv.note },
    ];
  },
  self: () => [{ key: 'tree', label: 'Parse tree: S at the root, each node’s children are the right side of one production, the leaves spell the string', marks: 0.5 }],
  Review({ d }) {
    const deriv = G.findDerivation(d.g, d.word);
    const tree = deriv ? G.treeFromForms(d.g, deriv) : null;
    return (
      <div class="stack-sm">
        <Automaton states={d.nfa.states} start={d.nfa.start} accept={d.nfa.accept} edges={M.mergedEdges(d.nfa)} last={['Qf']} />
        <div class="small muted">One state per variable plus the accepting state <MathText text="Q_f" />: <MathText text="A ⇒ aB" /> gives <MathText text="A —a→ B" />, <MathText text="A ⇒ a" /> gives <MathText text="A —a→ Q_f" />, and <MathText text="S ⇒ λ" /> gives <MathText text="S —λ→ Q_f" />.</div>
        {deriv && <div class="model-line"><MathText text={deriv.map(ft).join(' ⇒ ')} /></div>}
        {tree && <ParseTree root={tree} isVar={(s) => d.g.V.includes(s)} />}
      </div>
    );
  },
};

// ---- CFG derivation, parse tree, describe L(G)
const CFG_MOCK = ['t24q4', 't25q4', 't23q2', 'tut6q5', 'gram3', 'gram1-ex2', 'gram1-ex3', 'gram1-ex4'];
KINDS.cfg = {
  topic: 'Grammars & automata',
  drill: (d) => ({ id: 'g-derive', preset: { cfg: d.b.id } }),
  gen(rng, opt) {
    const id = rng.pick(CFG_MOCK);
    const b = CFG_BANK.find((x) => x.id === id);
    const g = G.parseGrammar(b.text).g;
    return { b, g, word: rng.pick(b.targets), opts: opt.describe ? rng.shuffle([b.desc, ...b.wrong]) : null, split: opt.describe ? { d: 2, t: 1 } : { d: 3, t: 2 } };
  },
  Q({ d, a, set, n, locked }) {
    return (
      <>
        <div class="qtext">Let G be the context-free grammar below.</div>
        <GrammarBox g={d.g} />
        <Part label={<>{d.opts ? '(a) ' : ''}Give a derivation for the string <Str>{d.word}</Str>,</>} marks={d.split.d}>
          <DerivField id={`m${n}-d`} value={a.deriv} set={(v) => set('deriv', v)} g={d.g} word={d.word} extra={d.g.V} />
        </Part>
        <Part label="and a parse tree." marks={d.split.t}><div class="small faint">Draw the tree on paper. After you submit you’ll see the model tree and tick it if yours matches.</div></Part>
        {d.opts && (
          <Part label="(b) Briefly describe the strings in L(G)." marks={1}>
            <Options options={d.opts} picked={a.desc ?? null} onPick={(i) => set('desc', i)} reveal={locked} correct={d.opts.indexOf(d.b.desc)} />
          </Part>
        )}
      </>
    );
  },
  auto(d, a) {
    const dv = gradeDeriv(a.deriv, [d.g], d.word);
    const out = [{ label: <>Derivation of <Str>{d.word}</Str></>, got: dv.ok ? d.split.d : 0, max: d.split.d, note: dv.note }];
    if (d.opts) out.push({ label: 'Describing L(G)', got: d.opts[a.desc] === d.b.desc ? 1 : 0, max: 1, note: d.b.desc });
    return out;
  },
  self: (d) => [{ key: 'tree', label: 'Parse tree: S at the root, each node’s children are the right side of one production, the leaves read the string left to right', marks: d.split.t }],
  Review({ d, a }) {
    const mine = gradeDeriv(a.deriv, [d.g], d.word).ok ? G.parseDerivation(norm(a.deriv), d.g) : null;
    const forms = mine || G.findDerivation(d.g, d.word);
    const tree = forms ? G.treeFromForms(d.g, forms) : null;
    return (
      <div class="stack-sm">
        {forms && <div class="model-line"><MathText text={forms.map(ft).join(' ⇒ ')} /></div>}
        {tree && <><div class="label">{mine ? 'The parse tree for your derivation' : 'Parse tree'}</div><ParseTree root={tree} isVar={(s) => d.g.V.includes(s)} /></>}
        {d.opts && <div class="model-line">{d.b.desc}</div>}
      </div>
    );
  },
};

// ---- a context-sensitive grammar that is not context-free
KINDS.cs = {
  topic: 'Grammars & automata',
  drill: () => ({ id: 'g-cs', preset: { cs: 't24q6' } }),
  gen: () => ({}),
  Q({ a, set, n }) {
    return (
      <>
        <div class="qtext">Give an example of a context-sensitive grammar that is not context-free.</div>
        <MathField id={`m${n}-g`} kind="gram" syms="gram" rows={3} hidePreview value={a.text || ''} setValue={(v) => set('text', typeof v === 'function' ? v(a.text || '') : v)} label="Productions P (variables are capital letters, S is the start symbol)" placeholder="S ⇒ …" />
      </>
    );
  },
  auto(d, a) {
    const max = d.marks;
    if (!(a.text || '').trim()) return [{ label: 'Example grammar', got: 0, max, note: 'No answer.' }];
    const r = G.parseGrammar(norm(a.text));
    if (!r.ok) return [{ label: 'Example grammar', got: 0, max, note: r.errors[0] }];
    const c = G.classify(r.g);
    if (c.type === 'context-sensitive') return [{ label: 'Example grammar', got: max, max, note: `Context-sensitive, and not context-free because of ${c.why.cf[0]}.` }];
    if (c.type === 'unrestricted') return [{ label: 'Example grammar', got: 0, max, note: `Not context-sensitive by the course definition: ${c.why.cs[0]}.` }];
    return [{ label: 'Example grammar', got: 0, max, note: `Every production has a single variable on the left, so this grammar is context-free (${G.TYPE_LABEL[c.type].toLowerCase()}).` }];
  },
  Review: () => (
    <div class="stack-sm">
      <div class="model-line"><MathText text="Here’s one: G = (V, T, S, P) where V = {S, A}, T = {0, 1} and P = {S ⇒ 0A, 0A ⇒ 00A | 00}." /></div>
      <div class="small muted">0A ⇒ 00A has a terminal on the left (context 0), so the grammar is not context-free, but each production has the form βAγ ⇒ βαγ with α non-empty.</div>
    </div>
  ),
};

// ---- true / false on the hierarchy and decidability
const TF_POOL = HIER_TF.filter((q) => q.src !== '2024 Test 2 Q9(c)');
KINDS.tf = {
  topic: 'Grammars & automata',
  drill: () => ({ id: 'g-classify', preset: { tab: 'tf' } }),
  gen: (rng, opt) => ({ qs: rng.sample(TF_POOL, opt.n) }),
  Q({ d, a, set }) {
    return (
      <>
        <div class="qtext">Are the following statements true or false? (½ mark each)</div>
        <div class="stack-sm">{d.qs.map((q, i) => (
          <div key={i} class="tfrow">
            <span class="tf-n">({LETTERS[i]})</span><span class="tf-s">{q.s}</span>
            <Seg value={a['t' + i] ?? null} onChange={(v) => set('t' + i, v)} label={`Statement ${LETTERS[i]}`} options={[{ value: true, label: 'True' }, { value: false, label: 'False' }]} />
          </div>
        ))}</div>
      </>
    );
  },
  auto: (d, a) => d.qs.map((q, i) => ({ label: `(${LETTERS[i]}) ${q.a ? 'True' : 'False'}`, got: a['t' + i] === q.a ? 0.5 : 0, max: 0.5, note: a['t' + i] === undefined || a['t' + i] === null ? `No answer. ${q.why}` : q.why })),
};

// ---- logical status by truth table
const STATUS_OPTS = [['valid', 'Valid (a tautology)'], ['satisfiable', 'Satisfiable but not valid'], ['unsatisfiable', 'Unsatisfiable (a contradiction)']];
function statusLines(f, st, vs) {
  const env = (e) => vs.map((v) => `${v} = ${TF(e[v])}`).join(', ');
  if (st.valid) return [`Every row of the column for P is T, so P = ${P.show(f)} is valid (a tautology).`];
  if (st.unsatisfiable) return [`Every row of the column for P is F, so P = ${P.show(f)} is unsatisfiable: it has no models.`];
  return [`P is not valid: ${env(st.counterexamples[0])} is a counterexample.`, `P is satisfiable: ${env(st.models[0])} is a model.`];
}
function tableErrors(cols, j, vs, cells) {
  let wrong = 0, empty = 0;
  const bad = new Set();
  P.rows(vs).forEach((env, i) => {
    const k = `${j}-${i}`;
    const v = (cells || {})[k];
    if (!v) empty++;
    else if (v !== TF(P.evaluate(cols[j], env))) { wrong++; bad.add(k); }
  });
  return { wrong, empty, bad };
}
function allWrong(cols, vs, cells) {
  const bad = new Set();
  cols.forEach((c, j) => P.rows(vs).forEach((env, i) => { const k = `${j}-${i}`; if (cells?.[k] && cells[k] !== TF(P.evaluate(c, env))) bad.add(k); }));
  return bad;
}
KINDS.status = {
  topic: 'Propositional logic',
  drill: (d) => ({ id: 'p-table', preset: { table: { mode: 'status', a: P.show(d.f), src: 'Mock test' } } }),
  gen(rng) {
    let f;
    if (rng.chance(0.45)) f = P.parse(rng.pick(STATUS_BANK).f);
    else { const vs = rng.chance(0.5) ? ['p', 'q', 'r'] : ['p', 'q']; f = genWff(rng, vs, { min: 5, max: vs.length === 3 ? 8 : 7 }); }
    const vs = P.vars(f);
    return { f, vs, cols: P.subformulas(f), st: P.status(f, vs) };
  },
  Q({ d, a, set, locked }) {
    return (
      <>
        <div class="qtext">Let P be the WFF <MathText text={`P = ${P.show(d.f)}`} />. Determine the logical status of P using a truth table.</div>
        <Part label="Truth table (click a cell, or focus it and type T or F). The column for P is marked; the others are your working." marks={2}>
          <TruthTable vs={d.vs} cols={d.cols} cells={a.cells || {}} setCell={(k, v) => set('cells', (c) => ({ ...(c || {}), [k]: v }))} answerCols={[d.cols.length - 1]} readOnly={locked} wrong={locked ? allWrong(d.cols, d.vs, a.cells) : null} />
        </Part>
        <Part label="So P is" marks={1}>
          <Options options={STATUS_OPTS.map((o) => o[1])} picked={STATUS_OPTS.findIndex((o) => o[0] === a.status)} onPick={(i) => set('status', STATUS_OPTS[i][0])} reveal={locked} correct={STATUS_OPTS.findIndex((o) => o[0] === d.st.label)} />
        </Part>
      </>
    );
  },
  auto(d, a) {
    const e = tableErrors(d.cols, d.cols.length - 1, d.vs, a.cells);
    const bad = e.wrong + e.empty;
    return [
      { label: 'Truth table (column for P)', got: bad === 0 ? 2 : bad === 1 ? 1 : 0, max: 2, note: bad ? `${e.wrong} wrong, ${e.empty} empty.` : 'Every row right.' },
      { label: 'Logical status', got: a.status === d.st.label ? 1 : 0, max: 1, note: statusLines(d.f, d.st, d.vs).join(' ') },
    ];
  },
  Review({ d }) {
    return (
      <div class="stack-sm">
        <TruthTable vs={d.vs} cols={d.cols} values readOnly answerCols={[d.cols.length - 1]} />
        {statusLines(d.f, d.st, d.vs).map((l, i) => <div key={i} class="model-line"><MathText text={l} /></div>)}
      </div>
    );
  },
};

// ---- functional completeness + an equivalence by truth table (2024 Q7)
const FC_EQUIV = [
  { a: 'p ↑ q', b: '(p ∧ q) → F' },
  { a: 'p ∨ q', b: '(p → F) → q' },
  { a: 'p ∧ q', b: '(p ↑ q) ↑ (p ↑ q)' },
  { a: 'p ∨ q', b: '(p ↑ p) ↑ (q ↑ q)' },
  { a: 'p ∨ q', b: '(p ↓ q) ↓ (p ↓ q)' },
  { a: 'p ↔ q', b: '(p → q) ∧ (q → p)' },
  { a: 'p ⊕ q', b: '(p ∨ q) ∧ ¬(p ∧ q)' },
];
const FC_CONCL = ['The columns for the two WFFs agree in every row, so they are logically equivalent.', 'The columns agree in at least one row, so they are logically equivalent.', 'Wherever the left WFF is T the right one is T, so only one is a consequence of the other.', 'The columns differ, so they are not equivalent.'];
KINDS.fc = {
  topic: 'Propositional logic',
  drill: (d) => ({ id: 'p-table', preset: { table: { mode: 'equiv', a: P.show(d.fa), b: P.show(d.fb), src: 'Mock test' } } }),
  gen(rng) {
    const e = rng.pick(FC_EQUIV);
    const fa = P.parse(e.a), fb = P.parse(e.b);
    const vs = P.vars(fa, fb);
    const ca = P.subformulas(fa), cb = P.subformulas(fb);
    const keys = new Set(ca.map(P.key));
    const cols = [...ca, ...cb.filter((c) => !keys.has(P.key(c)))];
    return { fa, fb, vs, cols, ia: cols.findIndex((c) => P.same(c, fa)), ib: cols.findIndex((c) => P.same(c, fb)), t: THEORY.find((x) => x.id === 'fc'), concl: rng.shuffle([0, 1, 2, 3]) };
  },
  Q({ d, a, set, n, locked }) {
    return (
      <>
        <Part label="(a) In propositional logic, what does it mean to say that a set of connectives is functionally complete?" marks={1}>
          <WrittenBox id={`m${n}-w`} value={a.text} set={(v) => set('text', v)} rows={3} />
        </Part>
        <Part label={<>(b) Prove that <MathText text={`${P.show(d.fa)} ⇔ ${P.show(d.fb)}`} />.</>} marks={4}>
          <TruthTable vs={d.vs} cols={d.cols} cells={a.cells || {}} setCell={(k, v) => set('cells', (c) => ({ ...(c || {}), [k]: v }))} answerCols={[d.ia, d.ib]} readOnly={locked} wrong={locked ? allWrong(d.cols, d.vs, a.cells) : null} />
          <div class="label">Conclusion</div>
          <Options options={d.concl.map((i) => FC_CONCL[i])} picked={d.concl.indexOf(a.concl)} onPick={(i) => set('concl', d.concl[i])} reveal={locked} correct={d.concl.indexOf(0)} />
        </Part>
      </>
    );
  },
  auto(d, a) {
    const ea = tableErrors(d.cols, d.ia, d.vs, a.cells), eb = tableErrors(d.cols, d.ib, d.vs, a.cells);
    const bad = ea.wrong + ea.empty + eb.wrong + eb.empty;
    return [
      { label: '(b) Truth table columns for both WFFs', got: bad === 0 ? 3 : bad <= 2 ? 2 : bad <= 4 ? 1 : 0, max: 3, note: bad ? `${ea.wrong + eb.wrong} wrong, ${ea.empty + eb.empty} empty in the two final columns.` : 'Both columns right.' },
      { label: '(b) Conclusion', got: a.concl === 0 ? 1 : 0, max: 1, note: FC_CONCL[0] },
    ];
  },
  written(d, a) { return [{ key: 'fc', label: '(a) Functional completeness', question: d.t.q, marks: 1, model: d.t.model, scheme: d.t.scheme, notes: '', answer: a.text || '' }]; },
  Review({ d }) {
    return (
      <div class="stack-sm">
        <TruthTable vs={d.vs} cols={d.cols} values readOnly answerCols={[d.ia, d.ib]} />
        <div class="model-line">The two marked columns are identical in every row, so {P.show(d.fa)} ⇔ {P.show(d.fb)}.</div>
      </div>
    );
  },
};

// ---- WFF from a truth table / description
KINDS.dnf = {
  topic: 'Propositional logic',
  drill: (d) => ({ id: 'p-dnf', preset: d.desc ? { words: true } : { vals: d.tt.map((r) => r.value) } }),
  gen(rng, opt) {
    if (opt.words) { const s = rng.pick(DNF_SPECIAL); return { desc: s.desc, target: P.parse(s.f), vs: s.vars }; }
    const vs = ['p', 'q', 'r'];
    const rs = P.rows(vs);
    let vals;
    do { const k = rng.int(2, 4); const on = new Set(rng.sample([...rs.keys()], k)); vals = rs.map((_, i) => on.has(i)); } while (vals.every((v) => !v));
    const tt = rs.map((env, i) => ({ env, value: vals[i] }));
    return { tt, vs, target: P.fullDNF(tt, vs) };
  },
  Q({ d, a, set, n }) {
    return (
      <>
        {d.desc ? <div class="qtext">{d.desc}</div> : (
          <>
            <div class="qtext">Write down a WFF P involving p, q, r that has the following truth table.</div>
            <div class="scroll-x"><table class="tt"><thead><tr>{d.vs.map((v) => <th key={v}><i>{v}</i></th>)}<th class="ans"><i>P</i></th></tr></thead>
              <tbody>{d.tt.map((r, i) => <tr key={i}>{d.vs.map((v) => <td key={v} class="var">{TF(r.env[v])}</td>)}<td class="ans">{TF(r.value)}</td></tr>)}</tbody></table></div>
          </>
        )}
        <MathField id={`m${n}-f`} value={a.f || ''} setValue={(v) => set('f', typeof v === 'function' ? v(a.f || '') : v)} placeholder="e.g. (¬p ∧ q ∧ ¬r) ∨ (p ∧ q ∧ r)" label="P =" />
      </>
    );
  },
  auto(d, a) {
    const max = d.marks;
    if (!(a.f || '').trim()) return [{ label: 'WFF', got: 0, max, note: 'No answer.' }];
    const p = P.tryParse(a.f);
    if (!p.ok) return [{ label: 'WFF', got: 0, max, note: `Couldn’t read it: ${p.error}` }];
    const extra = P.vars(p.ast).filter((v) => !d.vs.includes(v));
    if (extra.length) return [{ label: 'WFF', got: 0, max, note: `Only use ${d.vs.join(', ')}.` }];
    const eq = P.equivalent(p.ast, d.target);
    if (eq.equiv) return [{ label: 'WFF', got: max, max, note: 'Same truth value in every row.' }];
    const env = { ...Object.fromEntries(d.vs.map((v) => [v, false])), ...eq.env };
    return [{ label: 'WFF', got: 0, max, note: `With ${d.vs.map((v) => `${v} = ${TF(env[v])}`).join(', ')} yours is ${TF(eq.a)} but P is ${TF(eq.b)}.` }];
  },
  Review({ d }) {
    const full = P.fullDNF(P.truthTable(d.target, d.vs), d.vs);
    return (
      <div class="stack-sm">
        <div class="model-line"><MathText text={`P could be ${P.show(full)}.`} /></div>
        {d.desc && <div class="model-line"><MathText text={`More simply, P ⇔ ${P.show(d.target)}.`} /></div>}
        <div class="small muted">One conjunction for each row where P is T, joined with ∨ (a full disjunctive normal form).</div>
      </div>
    );
  },
};

// ---- NAND only
const workingLines = (t) => (t || '').split('\n').map((l) => l.replace(/^\s*(⇔|<=>|<->|=|≡)\s*/, '').replace(/\([^()]*(law|morgan|negation|rule|nand|def)[^()]*\)\s*$/i, '').trim()).filter(Boolean);
KINDS.nand = {
  topic: 'Propositional logic',
  drill: (d) => ({ id: 'p-nand', preset: { nand: { f: P.show(d.f), target: 'nand', src: 'Mock test' } } }),
  gen(rng) {
    const r = rng.next();
    if (r < 0.4) return { f: P.parse(rng.pick(NAND_BANK.filter((b) => b.target === 'nand')).f) };
    if (r < 0.7) return { f: genWff(rng, ['p', 'q'], { min: 3, max: 5, ops: ['and', 'or', 'imp', 'and', 'or'] }) };
    return { f: genWff(rng, ['p', 'q', 'r'], { min: 4, max: 6, ops: ['and', 'or', 'and', 'or', 'imp'] }) };
  },
  Q({ d, a, set, n }) {
    return (
      <>
        <div class="qtext">Give a WFF involving only ↑ (NAND) that is logically equivalent to the WFF <MathText text={`P = ${P.show(d.f)}`} />, showing your reasoning.</div>
        <MathField id={`m${n}-w`} kind="nand" syms="nand" rows={4} hidePreview value={a.work || ''} setValue={(v) => set('work', typeof v === 'function' ? v(a.work || '') : v)} label="Working (one equivalent WFF per line)" placeholder={'⇔ …\n⇔ …'} />
        <MathField id={`m${n}-f`} kind="nand" syms="nand" value={a.final || ''} setValue={(v) => set('final', typeof v === 'function' ? v(a.final || '') : v)} label="Final answer (only ↑, with brackets)" placeholder="e.g. (p ↑ p) ↑ (q ↑ q)" />
      </>
    );
  },
  auto(d, a) {
    const max = d.marks;
    const L = 'WFF using only ↑';
    const lastWork = workingLines(a.work).slice(-1)[0] || '';
    const finalText = (a.final || '').trim() || lastWork;
    const fromWork = !(a.final || '').trim() && !!lastWork;
    if (!finalText) return [{ label: L, got: 0, max, note: 'No final answer.' }];
    const p = P.tryParse(finalText);
    if (!p.ok) return [{ label: L, got: 0, max, note: `Couldn’t read the final answer: ${p.error}` }];
    const r = checkRestricted(p.ast, d.f, 'nand');
    if (r.ok) return [{ label: L, got: max, max, note: `Equivalent, and it only uses ↑.${fromWork ? ' (Taken from your last line of working.)' : ''}` }];
    const progress = (f) => P.connectives(f).has('nand') && !P.same(f, d.f);
    if (r.equiv) {
      // nearly there: only ¬ is left to replace (¬A ⇔ A ↑ A)
      const part = progress(p.ast) && [...P.connectives(p.ast)].every((c) => c === 'nand' || c === 'not') ? 1 : 0;
      return [{ label: L, got: part, max, note: `Equivalent, but it still uses ${r.bad.map((b) => OPNAME[b] || b).join(' ')}.${part ? ' 1 mark: only the ¬s are left (¬A ⇔ A ↑ A).' : ''}` }];
    }
    const eq = P.equivalent(p.ast, d.f);
    const vs = P.vars(p.ast, d.f);
    const env = { ...Object.fromEntries(vs.map((v) => [v, false])), ...eq.env };
    const method = workingLines(a.work).some((l) => { const q = P.tryParse(l); return q.ok && progress(q.ast) && P.equivalent(q.ast, d.f).equiv; });
    return [{ label: L, got: method ? 1 : 0, max, note: `Not equivalent to P: with ${vs.map((v) => `${v} = ${TF(env[v])}`).join(', ')}, P is ${TF(eq.b)} but yours is ${TF(eq.a)}.${method ? ' 1 mark for correct working.' : ''}` }];
  },
  Review({ d }) {
    const sol = solutionSteps(d.f, 'nand');
    return <div class="stack-sm">{sol.map((s, i) => <div key={i} class={cx('model-line', i > 0 && 'indent')}><MathText text={i === 0 ? `P = ${P.show(s.f)}` : `⇔ ${P.show(s.f)}${s.why ? `   (${s.why})` : ''}`} /></div>)}</div>;
  },
};

// ---- argument validity (2023 Q5)
KINDS.argue = {
  topic: 'Propositional logic',
  drill: () => ({ id: 'p-argue' }),
  gen(rng) {
    const arg = makeArgument(rng.pick(FORMS), rng.pick(THEMES), rng.shuffle([0, 1, 2]));
    return { arg, fz: falsify(arg.premAst, arg.conclAst) };
  },
  Q({ d, a, set, n }) {
    return (
      <>
        <div class="qtext">For the following logical argument, carefully express it in terms of propositional logic by first defining suitable propositions, and write down a WFF which is a tautology if and only if the argument is valid, and hence prove or otherwise its validity.</div>
        <div class="panel" style={{ textAlign: 'center', fontSize: '16.5px' }}>
          {d.arg.premEn.map((s, i) => <div key={i}>“{s}”</div>)}
          <div><em>“{d.arg.conclEn.replace(/\.$/, '')}.”</em></div>
        </div>
        <WrittenBox id={`m${n}-w`} value={a.text} set={(v) => set('text', v)} rows={10} placeholder={'Let p = “…”, q = “…”, …\nThe argument is …\nIt is valid iff this WFF is a tautology: …\nTry to make it false: …'} />
      </>
    );
  },
  written(d, a) {
    const arg = d.arg;
    const model = [...arg.atoms.map((x) => `Let ${x.l} = “${x.m}”.`), `The argument is: ${arg.premAst.map((x) => P.show(x)).join(',  ')}  ∴ ${P.show(arg.conclAst)}.`, `It is valid iff this WFF is a tautology:  ${P.show(arg.wff)}.`, ...d.fz.lines].join('\n');
    return [{
      key: 'arg', label: 'Argument validity', marks: d.marks, model, answer: a.text || '',
      question: `Express this argument in propositional logic by first defining suitable propositions, write down a WFF which is a tautology if and only if the argument is valid, and hence prove or otherwise its validity: ${arg.premEn.map((s) => `“${s}”`).join(' ')} “${arg.conclEn.replace(/\.$/, '')}.”`,
      scheme: [{ p: 'Defines suitable atomic propositions (positive statements, with ¬ for “not”)', m: 1 }, { p: 'Translates each premise and the conclusion correctly', m: 2 }, { p: 'Writes the WFF (premise₁ ∧ premise₂ ∧ …) → conclusion', m: 1 }, { p: `Correct verdict (${d.fz.valid ? 'valid' : 'not valid'}) with a correct argument: trying to make the WFF false, a truth table, or a counterexample valuation`, m: 2 }],
      notes: 'Any letters may be used if they are defined. Accept ASCII connectives (->, ^, v, ~). For an invalid argument a single counterexample valuation (all premises T, conclusion F) is a complete proof.',
    }];
  },
  Review({ d }) {
    const arg = d.arg;
    return (
      <div class="stack-sm">
        {arg.atoms.map((x) => <div key={x.l} class="model-line">Let <MathText text={x.l} /> = “{x.m}”.</div>)}
        <div class="model-line"><MathText text={`The argument is: ${arg.premAst.map((x) => P.show(x)).join(',  ')}  ∴ ${P.show(arg.conclAst)}.`} /></div>
        <div class="model-line"><MathText text={`It is valid iff this WFF is a tautology:  ${P.show(arg.wff)}.`} /></div>
        {d.fz.lines.map((l, i) => <div key={i} class="model-line"><MathText text={l} /></div>)}
      </div>
    );
  },
};

// ---- predicate logic, both directions
const PRED_SCENS = ['dogs', 'music', 'cars', 'papers', 'friends'];
KINDS.pred = {
  topic: 'Predicate logic',
  drill: (d) => ({ id: 'q-translate', preset: { scen: d.scen } }),
  gen(rng, opt) {
    const scen = rng.pick(PRED_SCENS);
    const S = SCENARIOS[scen];
    const pool = sentences(scen);
    const easy = rng.shuffle(pool.filter((s) => s.lvl <= 2));
    const hard = pool.filter((s) => s.lvl === 3);
    let partA = easy.slice(0, opt.a);
    if (hard.length && rng.chance(0.5)) partA = [...partA.slice(0, opt.a - 1), rng.pick(hard)];
    const used = partA.map((s) => parsePred(s.f));
    const partB = [];
    for (const s of easy) {
      if (partB.length >= opt.b) break;
      if (partA.some((x) => x.id === s.id)) continue;
      const ast0 = parsePred(s.f);
      if (used.some((u) => comparePred(u, ast0, S.sig).equiv)) continue;
      used.push(ast0);
      partB.push({ ...s, ast: rng.chance(0.65) ? disguise(ast0, rng) : ast0 });
    }
    return { scen, partA, partB, splitB: opt.b };
  },
  Q({ d, a, set, n }) {
    const S = SCENARIOS[d.scen];
    const two = S.sig.sorts.length > 1;
    return (
      <>
        <div class="panel small">{S.setup}</div>
        <Part label="(a) State the following as propositions of predicate logic:" marks={d.partA.length}>
          {d.partA.map((s, i) => (
            <div key={s.id} class="stack-sm">
              <div>{ROMAN[i]}. “{s.en}”</div>
              <MathField id={`m${n}-a${i}`} kind="pred" value={a['a' + i] || ''} setValue={(v) => set('a' + i, typeof v === 'function' ? v(a['a' + i] || '') : v)} extraSyms={two ? ['∈', 'X', 'Y', 'P(x, y)'] : ['P(x, y)']} placeholder={two ? 'e.g. ∀x ∃y : P(x, y)' : 'e.g. ∃x ∀y : P(x, y)'} />
            </div>
          ))}
        </Part>
        <Part label="(b) Express the following in simplest possible English:" marks={d.partB.length}>
          {d.partB.map((s, i) => (
            <div key={s.id} class="stack-sm">
              <div>{ROMAN[i]}. <MathText text={showPred(s.ast)} /></div>
              <input class="input" value={a['b' + i] || ''} onInput={(e) => set('b' + i, e.currentTarget.value)} placeholder="In plain English…" aria-label={`English for part (b) ${ROMAN[i]}`} />
            </div>
          ))}
        </Part>
      </>
    );
  },
  auto(d, a) {
    const S = SCENARIOS[d.scen];
    return d.partA.map((s, i) => {
      const L = `(a) ${ROMAN[i]}.`;
      const txt = a['a' + i] || '';
      if (!txt.trim()) return { label: L, got: 0, max: 1, note: `No answer. One answer: ${s.f}` };
      const p = tryParsePred(txt);
      if (!p.ok) return { label: L, got: 0, max: 1, note: `Couldn’t read it: ${p.error}` };
      const r = comparePred(p.ast, parsePred(s.f), S.sig);
      if (r.error) return { label: L, got: 0, max: 1, note: r.error };
      if (r.equiv) return { label: L, got: 1, max: 1, note: `Correct${r.free.length ? ` (free ${r.free.join(', ')} read as “for all”; better to quantify)` : ''}.` };
      return { label: L, got: 0, max: 1, note: `${describeWorld(r.world, S)} There the sentence is ${r.ref ? 'true' : 'false'} but your formula is ${r.user ? 'true' : 'false'}. One answer: ${s.f}` };
    });
  },
  written(d, a) {
    const S = SCENARIOS[d.scen];
    const lines = d.partB.map((s, i) => {
      const shown = showPred(s.ast), simp = showPred(pushAll(s.ast));
      return `${ROMAN[i]}. ${shown !== simp ? `${shown} ⇔ ${simp}, so: ` : ''}${s.en}`;
    });
    return [{
      key: 'eng', label: '(b) Logic → English', marks: d.partB.length, answer: d.partB.map((_, i) => `${ROMAN[i]}. ${a['b' + i] || ''}`).join('\n'),
      question: `${S.setup} Express the following in simplest possible English: ${d.partB.map((s, i) => `${ROMAN[i]}. ${showPred(s.ast)}`).join('   ')}`,
      model: lines.join('\n'),
      scheme: d.partB.map((s, i) => ({ p: `${ROMAN[i]}. Same meaning as “${s.en}”`, m: 1 })),
      notes: 'Accept any wording with exactly the same meaning. The formulas may need simplifying first (generalised De Morgan, double negation): a correct but unsimplified literal reading (“it is not the case that there is no …”) earns ½. Swapping the roles of the two variables, or the quantifier order, earns 0 for that part.',
    }];
  },
  Review({ d }) {
    return (
      <div class="stack-sm">
        {d.partA.map((s, i) => <div key={s.id} class="model-line"><MathText text={`(a) ${ROMAN[i]}. ${s.f}`} /></div>)}
        {d.partB.map((s, i) => {
          const shown = showPred(s.ast), simp = showPred(pushAll(s.ast));
          return <div key={s.id} class="model-line"><MathText text={`(b) ${ROMAN[i]}. ${shown !== simp ? `${shown} ⇔ ${simp}: ` : ''}`} />{s.en}</div>;
        })}
      </div>
    );
  },
};

// ---- design a grammar + derivation (2023 Q3)
const DESIGN_MOCK = ['0n12n', '1n02n', 'pal', 'anbmcn', 'mgen', 'one1', 'astarba', 'endsbb', '0m1n', 'even0', 'abstar'];
KINDS.design = {
  topic: 'Grammars & automata',
  drill: (d) => ({ id: 'g-design', preset: { design: d.t.id } }),
  gen(rng) {
    const id = rng.pick(DESIGN_MOCK);
    const t = DESIGN.find((x) => x.id === id);
    let word = t.derive;
    if (!word) { const c = [...G.allStrings(t.alphabet, 6)].filter((w) => w.length >= 3 && t.test(w)); word = rng.pick(c); }
    return { t, word, model: G.parseGrammar(t.model).g };
  },
  Q({ d, a, set, n }) {
    const t = d.t;
    return (
      <>
        <div class="qtext">Design a {t.req ? `${t.req} ` : ''}grammar that generates the language L of <MathOrText text={t.title.replace(/ \(a regular grammar\)$/, '')} />{t.alphabet.length <= 3 ? <> (alphabet <MathText text={`{${t.alphabet.join(', ')}}`} />)</> : ''}, AND give a derivation of the string <Str>{d.word}</Str> using your grammar.</div>
        <Part label="Your grammar" marks={3}>
          <MathField id={`m${n}-g`} kind="gram" syms="gram" rows={4} hidePreview value={a.gram || ''} setValue={(v) => set('gram', typeof v === 'function' ? v(a.gram || '') : v)} placeholder={'S ⇒ …'} />
        </Part>
        <Part label={<>Derivation of <Str>{d.word}</Str></>} marks={1}>
          <MathField id={`m${n}-d`} kind="gram" syms="gram" rows={2} hidePreview value={a.deriv || ''} setValue={(v) => set('deriv', typeof v === 'function' ? v(a.deriv || '') : v)} placeholder={`S ⇒ … ⇒ ${d.word}`} />
        </Part>
      </>
    );
  },
  auto(d, a) {
    const t = d.t;
    let got = 0, note = 'No answer.', g = null;
    if ((a.gram || '').trim()) {
      const r = G.parseGrammar(norm(a.gram));
      if (!r.ok) note = r.errors[0];
      else {
        g = r.g;
        const c = G.checkDesign(r.g, { alphabet: t.alphabet, test: t.test, maxLen: t.maxLen, requireType: t.req });
        if (c.ok) { got = 3; note = c.message + (c.warning ? ` ${c.warning}` : ''); }
        else if (c.typeFail) {
          const c2 = G.checkDesign(r.g, { alphabet: t.alphabet, test: t.test, maxLen: t.maxLen, requireType: null });
          got = c2.ok ? 1.5 : 0; note = c.message + (c2.ok ? ' It does generate the right language.' : '');
        } else { got = c.missing != null && c.extra == null ? 1 : 0; note = c.message + (got ? ' (Part marks: everything it generates is in L.)' : ''); }
      }
    }
    const dv = gradeDeriv(a.deriv, [g, d.model], d.word);
    return [{ label: 'Grammar', got, max: 3, note }, { label: <>Derivation of <Str>{d.word}</Str></>, got: dv.ok ? 1 : 0, max: 1, note: dv.note }];
  },
  Review({ d }) {
    const deriv = G.findDerivation(d.model, d.word);
    return (
      <div class="stack-sm">
        {d.t.model.split('\n').map((l) => <div key={l} class="model-line"><MathText text={l} /></div>)}
        {deriv && <div class="model-line"><MathText text={deriv.map(ft).join(' ⇒ ')} /></div>}
        {d.t.alt && <div class="small muted">{d.t.alt}</div>}
      </div>
    );
  },
};

// ---- induction (ordinary or strong), written
function nextTerms(prob) {
  const fns = functionsFor(prob);
  const top = Math.max(...Object.keys(prob.seq.init).map(Number));
  return [top + 1, top + 2].map((i) => ({ i, v: A.show(fns.a(A.Q(i))) }));
}
KINDS.ind = {
  topic: 'Induction',
  drill: (d) => ({ id: d.prob.strong ? 'i-strong' : 'i-proof', preset: BANK.some((p) => p.id === d.prob.id) ? { ind: d.prob.id } : null }),
  gen(rng, opt, marks, ctx) {
    let prob;
    if (opt.strong) {
      prob = rng.chance(0.2) ? generated('stamps', rng.int(1, 1e9)) : rng.chance(0.15) ? generated('recur', rng.int(1, 1e9)) : rng.pick(BANK.filter((p) => p.strong));
    } else {
      const pool = BANK.filter((p) => !p.strong && p.kind !== 'stamps' && p.id !== 'ineq-2n2' && !ctx.used.has(p.id));
      prob = rng.chance(0.15) ? generated('div', rng.int(1, 1e9)) : rng.pick(pool);
    }
    ctx.used.add(prob.id);
    const terms = opt.strong && prob.seq && Object.keys(prob.seq.init).length === 2 ? nextTerms(prob) : null;
    return { prob, terms, proofMarks: terms ? marks - 1 : marks };
  },
  Q({ d, a, set, n }) {
    return (
      <>
        <div class="qtext">{d.prob.ask}</div>
        {d.terms && (
          <Part label={`(a) Compute ${d.terms.map((t) => `a${subn(t.i)}`).join(' and ')}.`} marks={1}>
            <div class="row">{d.terms.map((t) => (
              <label key={t.i} class="row" style={{ gap: '6px' }}><MathText text={`a${subn(t.i)} =`} /><input class="input mid" value={a['t' + t.i] || ''} onInput={(e) => set('t' + t.i, e.currentTarget.value)} /></label>
            ))}</div>
          </Part>
        )}
        <Part label={d.terms ? '(b) Hence use strong induction to prove the statement.' : 'Your proof'} marks={d.proofMarks}>
          <WrittenBox id={`m${n}-w`} value={a.text} set={(v) => set('text', v)} rows={13} placeholder={PROOF_PLACEHOLDER} />
        </Part>
      </>
    );
  },
  auto(d, a) {
    if (!d.terms) return [];
    return d.terms.map((t) => {
      const ok = (a['t' + t.i] || '').replace(/[\s.]/g, '').replace(/−/g, '-').replace(/^a\d+=/, '') === t.v;
      return { label: `(a) a${subn(t.i)}`, got: ok ? 0.5 : 0, max: 0.5, note: `a${subn(t.i)} = ${t.v}.` };
    });
  },
  written(d, a) {
    return [{ key: 'proof', label: d.terms ? '(b) Strong induction proof' : 'Induction proof', question: d.prob.ask, marks: d.proofMarks, model: modelProof(d.prob).join('\n'), scheme: proofScheme(d.prob, d.proofMarks), notes: PROOF_NOTES + (d.prob.note ? ` ${d.prob.note}` : ''), answer: a.text || '' }];
  },
  Review({ d }) {
    return (
      <div class="stack-sm">
        {d.terms && <div class="model-line"><MathText text={`(a) ${d.terms.map((t) => `a${subn(t.i)} = ${t.v}`).join(',  ')}.`} /></div>}
        {modelProof(d.prob).map((l, i) => <div key={i} class={cx('model-line', /^\s{2,}/.test(l) && 'indent')}><MathText text={l.trim()} /></div>)}
      </div>
    );
  },
};

// ---------------------------------------------------------------- paper shapes (each 40 marks)
export const SHAPES = {
  2025: {
    title: 'Like 2025', rec: true,
    list: 'Turing number · halting problem · DFSA → regular grammar · derivation and parse tree · undecidable problems · logical status · WFF from a truth table · NAND · predicate logic · induction',
    items: [['tm60', 4], ['theory', 4, { ids: ['halting'] }], ['fa2reg', 7, { form: 'table' }], ['cfg', 5], ['theory', 2, { ids: ['undecidable'] }],
      ['status', 3], ['dnf', 1], ['nand', 3], ['pred', 5, { a: 3, b: 2 }], ['ind', 6]],
  },
  2024: {
    title: 'Like 2024',
    list: 'Turing number · universal TMs · DFSA → grammar · derivation and L(G) · an undecidable CFG problem · a context-sensitive grammar · functional completeness · predicate logic · true/false · induction · strong induction',
    items: [['tm60', 4], ['theory', 3, { ids: ['utm'] }], ['fa2reg', 3, { form: 'diagram' }], ['cfg', 4, { describe: true }], ['theory', 1, { ids: ['undecidableCFG'] }],
      ['cs', 2], ['fc', 5], ['pred', 4, { a: 2, b: 2 }], ['tf', 3, { n: 6 }], ['ind', 5], ['ind', 6, { strong: true }]],
  },
  2023: {
    title: 'Like 2023',
    list: 'Halting problem · regular grammar → NFSA · design a grammar · hierarchy true/false · argument validity · WFF from a description · NAND · predicate logic · two induction proofs',
    items: [['theory', 4, { ids: ['halting'] }], ['reg2nfsa', 5], ['design', 4], ['tf', 2, { n: 4 }], ['argue', 6], ['dnf', 1, { words: true }],
      ['nand', 4], ['pred', 4, { a: 2, b: 2 }], ['ind', 5], ['ind', 5]],
  },
};

export function genPaper(seed, shapeId) {
  const shape = SHAPES[shapeId] || SHAPES[2025];
  const ctx = { used: new Set() };
  const items = shape.items.map(([kind, marks, opt = {}], i) => {
    const rng = new Rng((seed * 31 + 7919 * (i + 1)) >>> 0);
    const d = KINDS[kind].gen(rng, opt, marks, ctx);
    return { n: String(i + 1), kind, marks, d: { ...d, marks } };
  });
  return { items, total: items.reduce((s, x) => s + x.marks, 0) };
}

// ---------------------------------------------------------------- marking
const safely = (f, fallback) => { try { return f(); } catch (e) { console.error(e); return fallback; } };
export function markPaper(paper, st) {
  return paper.items.map((it) => {
    const K = KINDS[it.kind];
    const a = st.ans?.[it.n] || {};
    const auto = K.auto ? safely(() => K.auto(it.d, a), [{ label: 'Your answer', got: 0, max: it.marks, note: 'This answer couldn’t be marked automatically (something in it confused the checker). Compare it with the model answer.' }]) : [];
    const written = K.written ? safely(() => K.written(it.d, a), []).map((w) => ({ ...w, key: `${it.n}:${w.key}` })) : [];
    const self = K.self ? safely(() => K.self(it.d, a), []).map((s) => ({ ...s, key: `${it.n}:${s.key}` })) : [];
    let got = auto.reduce((s, p) => s + p.got, 0);
    let pending = 0;
    for (const w of written) {
      const sc = writtenScore(w, st);
      if (sc == null) pending += w.marks; else got += sc;
    }
    for (const s of self) if (st.self?.[s.key]) got += s.marks;
    return { it, a, auto, written, self, got, pending };
  });
}
function writtenScore(w, st) {
  if (!w.answer.replace(/^[ivx]+\.\s*$/gm, '').trim()) return 0;
  const c = st.claude?.[w.key];
  if (c) return Math.min(w.marks, c.score);
  const ticks = st.selfw?.[w.key];
  if (ticks && Object.keys(ticks).length) return w.scheme.reduce((s, p, i) => s + (ticks[i] ? p.m : 0), 0);
  return null;
}

const CODES = {
  not_granted: 'Claude marking isn’t allowed for this page in your browser, so mark this one with the checklist.',
  sampling_disabled: 'Claude isn’t available on your account here, so mark this one with the checklist.',
  rate_limited: 'Claude is busy or you’ve hit a usage limit. Try again shortly, or use the checklist.',
  session_expired: 'Sign in to Claude again to use marking, or use the checklist.',
  invalid_json: 'The marking came back garbled. Try again.',
  refused: 'Claude declined to mark this answer. Use the checklist.',
  not_declared: 'Claude marking isn’t switched on for this page, so use the checklist.',
  capability_disabled: 'Claude marking isn’t available in this view, so use the checklist.',
  capability_removed: 'This Claude app is too old for marking here, so use the checklist.',
  empty_completion: 'Claude returned an empty mark. Try again, or use the checklist.',
  upstream_error: 'The connection to Claude dropped. Try again in a moment.',
};

function useNow(ms) {
  const [now, setNow] = useState(Date.now());
  useEffect(() => { if (!ms) return undefined; const t = setInterval(() => setNow(Date.now()), ms); return () => clearInterval(t); }, [ms]);
  return now;
}
const clock = (ms) => { const s = Math.max(0, Math.round(ms / 1000)); return `${Math.floor(s / 60)}:${String(s % 60).padStart(2, '0')}`; };

// ---------------------------------------------------------------- page
export function MockPage() {
  const [st, setSt] = useState(() => { const s = loadMock(); return s && s.v === 1 && s.seed && SHAPES[s.shape] ? s : null; });
  useEffect(() => { saveMock(st); }, [st]);
  if (!st) return <MockStart onStart={(shape, timed) => { setSt({ v: 1, id: `m${Date.now()}`, seed: newSeed(), shape, timed, startedAt: Date.now(), ans: {} }); window.scrollTo({ top: 0 }); }} />;
  return <MockRun key={st.id} st={st} setSt={setSt} />;
}

function MockStart({ onStart }) {
  const [shape, setShape] = useState('2025');
  const [timed, setTimed] = useState(true);
  const past = mocks().slice(-6).reverse();
  return (
    <div class="sheet">
      <header class="stack-sm">
        <div class="h-kicker">Mock test · 60 minutes · 40 marks</div>
        <h1 class="h-title">Sit a mock Test 2</h1>
        <p class="h-sub">A fresh paper generated in the format of a past test: the same question types and mark values, new numbers. No hints or checking until you submit; then everything is marked, with model answers in the lecturer’s layout. Written answers are marked by Claude when it’s available here, otherwise by you with a checklist.</p>
      </header>
      <section class="card stack">
        <div class="label">Paper format</div>
        <div class="shape-grid">
          {Object.entries(SHAPES).reverse().map(([id, s]) => (
            <button type="button" key={id} class={cx('opt', 'shape', shape === id && 'picked')} onClick={() => setShape(id)} aria-pressed={shape === id}>
              <span class="key">{shape === id ? '✓' : ''}</span>
              <span class="stack-sm"><span class="row" style={{ gap: '8px' }}><strong>{s.title}</strong>{s.rec && <Chip kind="blue">closest to this year</Chip>}</span><span class="small muted">{s.list}</span></span>
            </button>
          ))}
        </div>
        <div class="row">
          <Seg value={timed} onChange={setTimed} label="Timing" options={[{ value: true, label: '60-minute timer' }, { value: false, label: 'Untimed' }]} />
          <span class="small faint">{timed ? 'Submits itself when the time is up.' : 'Take as long as you like.'}</span>
        </div>
        <ul class="prose small muted" style={{ margin: 0 }}>
          <li>Have paper and a pen ready: some parts (parse trees) are drawn on paper and ticked off afterwards.</li>
          <li>As in the real test you get the Turing code table and the laws of equivalence; nothing else.</li>
          <li>Your answers are saved in this browser as you go, so a reload doesn’t lose them.</li>
        </ul>
        <div class="row"><Btn kind="primary" onClick={() => onStart(shape, timed)}>Start the test</Btn></div>
      </section>
      {past.length > 0 && (
        <section class="card stack-sm">
          <h2 class="h2">Your previous mock tests</h2>
          <table class="plain"><thead><tr><th>When</th><th>Format</th><th>Score</th></tr></thead>
            <tbody>{past.map((m) => <tr key={m.id || m.at}><td>{new Date(m.at).toLocaleString()}</td><td>{SHAPES[m.shape]?.title || m.shape}</td><td class="nums"><strong>{fmt(m.score)} / {m.max}</strong>{m.pending ? <span class="small faint"> (+{fmt(m.pending)} unmarked)</span> : null}</td></tr>)}</tbody></table>
        </section>
      )}
    </div>
  );
}

function MockRun({ st, setSt }) {
  const paper = useMemo(() => genPaper(st.seed, st.shape), [st.seed, st.shape]);
  const done = !!st.submittedAt;
  const now = useNow(done ? 0 : 1000);
  const left = st.startedAt + DURATION - now;
  const submit = (auto) => setSt((s) => (s.submittedAt ? s : { ...s, submittedAt: auto ? Math.min(Date.now(), s.startedAt + DURATION) : Date.now(), autoSubmitted: !!auto }));
  useEffect(() => { if (st.timed && !done && left <= 0) submit(true); }, [left <= 0, done]);
  useEffect(() => { if (done) window.scrollTo({ top: 0 }); }, [done]);
  const setAns = (n) => (key, v) => setSt((s) => {
    if (s.submittedAt) return s;
    const cur = s.ans?.[n] || {};
    const nv = typeof v === 'function' ? v(cur[key]) : v;
    return { ...s, ans: { ...(s.ans || {}), [n]: { ...cur, [key]: nv } } };
  });
  const marked = useMemo(() => (done ? markPaper(paper, st) : null), [done, paper, st.ans, st.claude, st.selfw, st.self]);
  const q = useClaudeQueue(marked, st, setSt);
  const [confirm, setConfirm] = useState(false);
  const shape = SHAPES[st.shape] || SHAPES[2025];
  return (
    <div class="sheet">
      {!done && (
        <div class="mockbar" role="region" aria-label="Test controls">
          <span class="mockbar-title">Mock · {shape.title}</span>
          <div class="qchips">{paper.items.map((it) => (
            <button type="button" key={it.n} class={cx('qchip', answered(st.ans?.[it.n]) && 'on')} onClick={() => document.getElementById(`mq${it.n}`)?.scrollIntoView({ behavior: 'smooth', block: 'start' })} aria-label={`Question ${it.n}${answered(st.ans?.[it.n]) ? ', answered' : ''}`}>{it.n}</button>
          ))}</div>
          <span class="spacer" />
          {st.timed ? <span class={cx('timer', left < 5 * 60000 && 'low')} aria-live="off">{clock(left)}</span> : <span class="timer faint">{clock(now - st.startedAt)}</span>}
          {confirm ? (
            <span class="row" style={{ gap: '6px' }}><Btn sm kind="primary" onClick={() => submit(false)}>Submit now</Btn><Btn sm kind="ghost" onClick={() => setConfirm(false)}>Keep going</Btn></span>
          ) : <Btn sm kind="primary" onClick={() => setConfirm(true)}>Submit</Btn>}
        </div>
      )}
      {done ? <ResultsHead st={st} paper={paper} marked={marked} q={q} /> : (
        <header class="paper-head">
          <div class="h-kicker">COMPX361-26B · Logic and Computation · Mock Test 2 ({shape.title.toLowerCase()})</div>
          <h1 class="h-title">Answer all questions. Total: {paper.total} marks. Time: 60 minutes.</h1>
          <div class="row">
            <Collapse title="Code table (supplied)"><CodeTable /></Collapse>
            <Collapse title="Laws of equivalence (supplied)"><LawSheet /></Collapse>
          </div>
        </header>
      )}
      {paper.items.map((it, idx) => {
        const K = KINDS[it.kind];
        const a = st.ans?.[it.n] || {};
        const m = marked?.[idx];
        return (
          <section key={it.n} id={`mq${it.n}`} class="mq">
            <div class="mq-head">
              <span class="qnum">Question {it.n}</span><Chip kind="marks">{fmt(it.marks)} mark{it.marks === 1 ? '' : 's'}</Chip>
              <span class="spacer" />
              {m && <span class={cx('mq-score', m.pending ? '' : m.got >= it.marks ? 'full' : m.got > 0 ? 'part' : 'zero')}>{fmt(m.got)}{m.pending ? `+?` : ''} / {fmt(it.marks)}</span>}
            </div>
            <fieldset class={cx('mq-body', done && 'locked')} disabled={done}>
              <K.Q d={it.d} a={a} set={setAns(it.n)} n={it.n} locked={done} />
            </fieldset>
            {m && <MarkPanel m={m} K={K} st={st} setSt={setSt} q={q} />}
          </section>
        );
      })}
      {!done && (
        <div class="row" style={{ justifyContent: 'flex-end' }}>
          {confirm ? <><span class="small muted">Submit your answers for marking?</span><Btn kind="primary" onClick={() => submit(false)}>Submit now</Btn><Btn kind="ghost" onClick={() => setConfirm(false)}>Keep going</Btn></>
            : <Btn kind="primary" onClick={() => setConfirm(true)}>Submit for marking</Btn>}
        </div>
      )}
      {done && <ResultsFoot st={st} setSt={setSt} />}
    </div>
  );
}

// ---------------------------------------------------------------- results
function useClaudeQueue(marked, st, setSt) {
  const enabled = !!marked;
  const [avail, setAvail] = useState(null);
  useEffect(() => {
    if (!enabled) return undefined;
    let live = true;
    getSample().then((s) => { if (live) setAvail(!!s); });
    return () => { live = false; };
  }, [enabled]);
  const [busy, setBusy] = useState(null);
  const ctl = useRef(null);
  const all = useMemo(() => (marked || []).flatMap((m) => m.written), [marked]);
  useEffect(() => () => ctl.current?.abort(), []);
  useEffect(() => {
    if (!avail || busy || st.claudeStop) return;
    const next = all.find((w) => w.answer.replace(/^[ivx]+\.\s*$/gm, '').trim() && !st.claude?.[w.key] && !st.claudeErr?.[w.key]);
    if (!next) return;
    setBusy(next.key);
    ctl.current = new AbortController();
    askMark({ question: next.question, marks: next.marks, model: next.model, scheme: next.scheme, answer: next.answer, notes: next.notes }, ctl.current.signal)
      .then((res) => setSt((s) => ({ ...s, claude: { ...(s.claude || {}), [next.key]: res } })))
      .catch((e) => {
        const code = e?.code || 'error';
        if (code === 'cancelled') return;
        setSt((s) => ({ ...s, claudeErr: { ...(s.claudeErr || {}), [next.key]: code }, claudeStop: s.claudeStop || ['not_granted', 'sampling_disabled', 'session_expired', 'not_declared', 'capability_disabled', 'capability_removed', 'rate_limited'].includes(code) }));
      })
      .finally(() => setBusy(null));
  }, [avail, busy, all, st.claude, st.claudeErr, st.claudeStop]);
  const retry = (key) => setSt((s) => { const e = { ...(s.claudeErr || {}) }; delete e[key]; return { ...s, claudeErr: e, claudeStop: false }; });
  return { avail, busy, retry, count: all.length };
}

function ResultsHead({ st, paper, marked, q }) {
  const total = marked.reduce((s, m) => s + m.got, 0);
  const pending = marked.reduce((s, m) => s + m.pending, 0);
  const autoMax = marked.reduce((s, m) => s + m.auto.reduce((t, p) => t + p.max, 0), 0);
  useEffect(() => { upsertMock({ id: st.id, score: total, max: paper.total, shape: st.shape, pending }); }, [total, pending]);
  const topics = {};
  for (const m of marked) {
    const t = KINDS[m.it.kind].topic;
    topics[t] = topics[t] || { got: 0, max: 0, pending: 0 };
    topics[t].got += m.got; topics[t].max += m.it.marks; topics[t].pending += m.pending;
  }
  const used = (st.submittedAt || Date.now()) - st.startedAt;
  return (
    <header class="card stack results-head">
      <div class="h-kicker">Mock test ({(SHAPES[st.shape] || SHAPES[2025]).title.toLowerCase()}) · marked</div>
      <div class="row" style={{ alignItems: 'baseline', gap: '16px' }}>
        <span class="score-big">{fmt(total)} / {paper.total}</span>
        {pending > 0 && <span class="muted">+ up to {fmt(pending)} still to mark below</span>}
        <span class="spacer" />
        <span class="small faint">{st.autoSubmitted ? 'Submitted automatically when time ran out' : `Time used: ${clock(used)}`}</span>
      </div>
      {q.busy && <Fb kind="info">Claude is marking your written answers against the model answers, one at a time. This can take a minute or two.</Fb>}
      {q.avail === false && q.count > 0 && <Fb kind="hint">Claude marking isn’t available here (it works when the page is opened {CLAUDE_URL ? <a href={CLAUDE_URL} target="_blank" rel="noopener">inside Claude</a> : 'inside Claude'}). Mark the written answers yourself: each has a model answer and a checklist.</Fb>}
      {st.claudeStop && <Fb kind="hint">Claude marking was turned down or isn’t available on this account, so use the checklists for the written answers.</Fb>}
      <div class="topic-bars">
        {Object.entries(topics).map(([t, x]) => (
          <div key={t} class="topic-bar">
            <div class="row" style={{ gap: '6px' }}><span class="small"><strong>{t}</strong></span><span class="spacer" /><span class="small nums">{fmt(x.got)}{x.pending ? '+?' : ''} / {fmt(x.max)}</span></div>
            <div class="bar"><span style={{ width: `${(100 * x.got) / x.max}%` }} /></div>
          </div>
        ))}
      </div>
      <p class="small faint">Auto-marked parts ({fmt(autoMax)} marks) use the same checks as the drills. Each question below shows your answer, the marks, the model answer and a link to practise it.</p>
    </header>
  );
}

function ResultsFoot({ st, setSt }) {
  const [sure, setSure] = useState(false);
  return (
    <div class="card row">
      <strong>Next</strong>
      <span class="spacer" />
      <Btn onClick={() => { setSt({ v: 1, id: `m${Date.now()}`, seed: st.seed, shape: st.shape, timed: st.timed, startedAt: Date.now(), ans: {} }); window.scrollTo({ top: 0 }); }}>Retake this paper</Btn>
      {sure ? <><Btn kind="primary" onClick={() => { setSt(null); window.scrollTo({ top: 0 }); }}>Yes, set a new paper</Btn><Btn kind="ghost" onClick={() => setSure(false)}>Cancel</Btn></>
        : <Btn kind="primary" onClick={() => setSure(true)}>New mock test</Btn>}
    </div>
  );
}

function MarkLine({ p }) {
  const full = p.got >= p.max, some = p.got > 0;
  return (
    <div class="mark-point">
      <span class={cx('m', full ? 'status ok' : !some && 'status bad')}>{full ? '✓' : some ? '½' : '✗'}</span>
      <div><strong>{p.label}</strong> <span class="muted">{/[∀∃¬∧∨→↔⊕↑↓⇒⇔]/.test(p.note || '') ? <MathText text={p.note} /> : p.note}</span></div>
      <span class="mono nums">{fmt(p.got)}/{fmt(p.max)}</span>
    </div>
  );
}

function WrittenMark({ w, st, setSt, q }) {
  const res = st.claude?.[w.key];
  const err = st.claudeErr?.[w.key];
  const ticks = st.selfw?.[w.key] || {};
  const empty = !w.answer.replace(/^[ivx]+\.\s*$/gm, '').trim();
  const busy = q.busy === w.key;
  const queued = !res && !err && !empty && q.avail && !st.claudeStop;
  const selfTotal = w.scheme.reduce((s, p, i) => s + (ticks[i] ? p.m : 0), 0);
  const tick = (i, v) => setSt((s) => ({ ...s, selfw: { ...(s.selfw || {}), [w.key]: { ...((s.selfw || {})[w.key] || {}), [i]: v } } }));
  return (
    <div class="wmark">
      <div class="row"><strong>{w.label}</strong><span class="chip">written</span><span class="spacer" />
        <span class="mono nums">{empty ? `0/${fmt(w.marks)}` : res ? `${fmt(res.score)}/${fmt(w.marks)}` : busy ? 'marking…' : queued ? 'queued' : `${fmt(selfTotal)}/${fmt(w.marks)}`}</span></div>
      {empty && <div class="small muted">No answer.</div>}
      {res && (
        <div class="stack-sm">
          {res.points.map((p, i) => (
            <div key={i} class="mark-point"><span class={cx('m', p.awarded >= p.max ? 'status ok' : p.awarded > 0 ? '' : 'status bad')}>{p.awarded >= p.max ? '✓' : p.awarded > 0 ? '½' : '✗'}</span>
              <div><strong>{p.point}</strong> <span class="muted">{p.comment}</span></div><span class="mono nums">{fmt(p.awarded)}/{fmt(p.max)}</span></div>
          ))}
          {res.feedback && <p class="small muted">{res.feedback}</p>}
          {res.fix && <Fb kind="hint">{res.fix}</Fb>}
          <span class="small faint">Marked by Claude against the model answer.</span>
        </div>
      )}
      {!res && !empty && !busy && !queued && (
        <div class="stack-sm">
          {err && <Fb kind="hint">{CODES[err] || 'Marking failed.'}{q.avail && <> <Btn sm onClick={() => q.retry(w.key)}>Try Claude again</Btn></>}</Fb>}
          <div class="label">Self-mark: tick what your answer has</div>
          {w.scheme.map((s, i) => (
            <label key={i} class="row" style={{ gap: '8px', alignItems: 'flex-start', flexWrap: 'nowrap' }}>
              <input type="checkbox" checked={!!ticks[i]} onChange={(e) => tick(i, e.currentTarget.checked)} />
              <span>{s.p} <span class="mono faint">[{fmt(s.m)}]</span></span>
            </label>
          ))}
          <div class="row">
            {!Object.keys(ticks).length && <Btn sm kind="ghost" onClick={() => setSt((s) => ({ ...s, selfw: { ...(s.selfw || {}), [w.key]: { none: true } } }))}>None of these (0 marks)</Btn>}
            {Object.keys(ticks).length > 0 && <span class="small faint">Self-marked: {fmt(selfTotal)} / {fmt(w.marks)}</span>}
          </div>
        </div>
      )}
      <Collapse title="Model answer">
        {w.model.split('\n').map((l, i) => <div key={i} class="model-line" style={{ fontFamily: 'var(--font-math)', fontSize: '16.5px' }}><MathText text={l} /></div>)}
      </Collapse>
    </div>
  );
}

function MarkPanel({ m, K, st, setSt, q }) {
  const dr = K.drill(m.it.d);
  const D = DRILLS[dr.id];
  return (
    <div class="mres">
      {m.auto.map((p, i) => <MarkLine key={i} p={p} />)}
      {m.written.map((w) => <WrittenMark key={w.key} w={w} st={st} setSt={setSt} q={q} />)}
      {m.self.map((s) => (
        <label key={s.key} class="selfrow">
          <input type="checkbox" checked={!!st.self?.[s.key]} onChange={(e) => { const v = e.currentTarget.checked; setSt((x) => ({ ...x, self: { ...(x.self || {}), [s.key]: v } })); }} />
          <span><strong>Self-mark:</strong> {s.label} <span class="mono faint">[{fmt(s.marks)}]</span></span>
        </label>
      ))}
      {K.Review && (
        <details class="sol" open={m.got < m.it.marks || m.pending > 0 || m.self.length > 0}>
          <summary>Model answer</summary>
          <div><K.Review d={m.it.d} a={m.a} /></div>
        </details>
      )}
      {D && <div class="row"><Btn sm onClick={() => window.__openDrill(dr.id, dr.preset || undefined)}>Practise: {D.title}</Btn></div>}
    </div>
  );
}
