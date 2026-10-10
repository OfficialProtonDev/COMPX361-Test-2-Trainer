// Finite automata for the grammar ↔ automaton conversions (GRAM2).
import { LAMBDA, parseGrammar, formText } from './gram.js';

// nfa = { states: [...], start, accept: [...], edges: [{from, to, label}] }   label: symbol or 'λ'

// Course construction: regular grammar → NFSA with one accepting state Qf.
export function grammarToNFSA(g) {
  const edges = [];
  for (const p of g.P) {
    const A = p.lhs[0];
    if (p.rhs.length === 0) edges.push({ from: A, to: 'Qf', label: LAMBDA });
    else if (p.rhs.length === 1) edges.push({ from: A, to: 'Qf', label: p.rhs[0] });
    else edges.push({ from: A, to: p.rhs[1], label: p.rhs[0] });
  }
  return { states: [...g.V, 'Qf'], start: g.S, accept: ['Qf'], edges: dedupe(edges) };
}

// Course construction: DFSA (or λ-free NFSA) → regular grammar.
export function automatonToGrammar(m) {
  const P = [];
  const add = (lhs, rhs) => { if (!P.some((p) => p.lhs[0] === lhs && p.rhs.join() === rhs.join())) P.push({ lhs: [lhs], rhs }); };
  for (const q of m.states) {
    for (const e of m.edges.filter((x) => x.from === q)) {
      add(q, [e.label, e.to]);
      if (m.accept.includes(e.to)) add(q, [e.label]);
    }
  }
  if (m.accept.includes(m.start)) add(m.start, []);
  const T = [...new Set(m.edges.map((e) => e.label))].sort();
  return { V: [...m.states], T, S: m.start, P };
}

function dedupe(edges) {
  const out = [];
  for (const e of edges) if (!out.some((x) => x.from === e.from && x.to === e.to && x.label === e.label)) out.push(e);
  return out;
}

export function fromDelta(states, alphabet, delta, start, accept) {
  const edges = [];
  for (const q of states) for (const a of alphabet) if (delta[q]?.[a] != null) edges.push({ from: q, to: delta[q][a], label: a });
  return { states, start, accept, edges, alphabet };
}

export function closureL(m, set) {
  const out = new Set(set);
  const stack = [...set];
  while (stack.length) {
    const q = stack.pop();
    for (const e of m.edges) if (e.from === q && e.label === LAMBDA && !out.has(e.to)) { out.add(e.to); stack.push(e.to); }
  }
  return out;
}

export function accepts(m, w) {
  let cur = closureL(m, [m.start]);
  for (const c of w) {
    const nx = new Set();
    for (const q of cur) for (const e of m.edges) if (e.from === q && e.label === c) nx.add(e.to);
    cur = closureL(m, nx);
  }
  return [...cur].some((q) => m.accept.includes(q));
}

// Deterministic run, returning the path q0 →a q1 → …
export function runDFSA(m, w) {
  const path = [m.start];
  let q = m.start;
  for (const c of w) {
    const e = m.edges.find((x) => x.from === q && x.label === c);
    if (!e) return { path, stuck: true, accepted: false };
    q = e.to; path.push(q);
  }
  return { path, accepted: m.accept.includes(q) };
}

export function sameEdges(a, b) {
  const k = (e) => `${e.from}|${e.label}|${e.to}`;
  const A = new Set(a.map(k)), B = new Set(b.map(k));
  const missing = [...A].filter((x) => !B.has(x)).map(unk);
  const extra = [...B].filter((x) => !A.has(x)).map(unk);
  return { same: !missing.length && !extra.length, missing, extra };
}
const unk = (s) => { const [from, label, to] = s.split('|'); return { from, label, to }; };

export function languageUpTo(m, alphabet, maxLen) {
  const out = new Set();
  const rec = (s) => { if (accepts(m, s)) out.add(s); if (s.length < maxLen) for (const a of alphabet) rec(s + a); };
  rec('');
  return out;
}

// Merge parallel edges for drawing: [{from, to, labels: [..]}]
export function mergedEdges(m) {
  const out = [];
  for (const e of m.edges) {
    let x = out.find((y) => y.from === e.from && y.to === e.to);
    if (!x) out.push((x = { from: e.from, to: e.to, labels: [] }));
    if (!x.labels.includes(e.label)) x.labels.push(e.label);
  }
  for (const x of out) x.labels.sort((a, b) => (a === LAMBDA ? -1 : b === LAMBDA ? 1 : a.localeCompare(b)));
  return out;
}

// ---------------------------------------------------------------- generators
export function randomDFSA(rng, { n = rng.pick([3, 3, 4]), alphabet = rng.pick([['a', 'b'], ['0', '1']]) } = {}) {
  for (let attempt = 0; attempt < 400; attempt++) {
    const states = Array.from({ length: n }, (_, i) => 'q' + i);
    const delta = {};
    for (const q of states) { delta[q] = {}; for (const a of alphabet) delta[q][a] = rng.pick(states); }
    const nAcc = rng.pick(n === 3 ? [1, 1, 2] : [1, 1, 2]);
    const accept = rng.sample(states.slice(1), nAcc);
    if (rng.chance(0.15)) accept.push('q0');
    const m = fromDelta(states, alphabet, delta, 'q0', accept);
    // every state reachable
    const seen = new Set(['q0']); const st = ['q0'];
    while (st.length) { const q = st.pop(); for (const a of alphabet) { const r = delta[q][a]; if (!seen.has(r)) { seen.add(r); st.push(r); } } }
    if (seen.size !== n) continue;
    // not trivial: language not empty, not everything; at most 2 self-loops per state used
    const L = languageUpTo(m, alphabet, 5);
    let total = 0; for (let k = 0; k <= 5; k++) total += alphabet.length ** k;
    if (L.size === 0 || L.size === total || L.size < 3) continue;
    // all states distinguishable (no redundant duplicate states)
    if (!minimal(m, alphabet)) continue;
    return { m, delta };
  }
  throw new Error('could not generate a DFSA');
}

function minimal(m, alphabet) {
  // Moore partition refinement
  let part = new Map(m.states.map((q) => [q, m.accept.includes(q) ? 1 : 0]));
  for (let round = 0; round < m.states.length; round++) {
    const sig = new Map(m.states.map((q) => [q, part.get(q) + ':' + alphabet.map((a) => part.get(m.edges.find((e) => e.from === q && e.label === a).to)).join(',')]));
    const ids = new Map(); const np = new Map();
    for (const q of m.states) { const s = sig.get(q); if (!ids.has(s)) ids.set(s, ids.size); np.set(q, ids.get(s)); }
    part = np;
  }
  return new Set(part.values()).size === m.states.length;
}

export function randomRegularGrammar(rng) {
  const T = rng.pick([['0', '1'], ['a', 'b'], ['a', 'b', 'c']]);
  const names = rng.pick([['S', 'A', 'B'], ['S', 'X', 'Y'], ['S', 'A']]);
  for (let attempt = 0; attempt < 300; attempt++) {
    const P = [];
    for (const v of names) {
      const k = rng.int(2, v === 'S' ? 3 : 3);
      const opts = [];
      for (const t of T) { for (const w of names.slice(1)) opts.push([t, w]); opts.push([t]); }
      for (const o of rng.sample(opts, k)) P.push({ lhs: [v], rhs: o });
    }
    if (rng.chance(0.45)) P.push({ lhs: ['S'], rhs: [] });
    const g = { V: names, T, S: 'S', P };
    // each variable reachable and productive, S has ≥2 productions, every non-S variable has a terminal exit
    const reach = new Set(['S']); let ch = true;
    while (ch) { ch = false; for (const p of P) if (reach.has(p.lhs[0]) && p.rhs[1] && !reach.has(p.rhs[1])) { reach.add(p.rhs[1]); ch = true; } }
    if (reach.size !== names.length) continue;
    if (names.slice(1).some((v) => !P.some((p) => p.lhs[0] === v && p.rhs.length === 1))) continue;
    if (P.filter((p) => p.lhs[0] === 'S').length < 2) continue;
    // some recursion so the NFSA has loops
    if (!P.some((p) => p.rhs[1] && p.rhs[1] === p.lhs[0])) continue;
    g.T = [...new Set(P.flatMap((p) => p.rhs.filter((t) => !names.includes(t))))].sort();
    return g;
  }
  return parseGrammar('S ⇒ 0A | 1B | λ, A ⇒ 0A | 1B | 1, B ⇒ 1B | 0A | 0').g;
}

// A string of the requested length range in L(nfa), with a derivation-friendly path.
export function sampleAccepted(m, alphabet, rng, minLen = 4, maxLen = 7) {
  const cands = [];
  for (let len = minLen; len <= maxLen; len++) {
    for (let t = 0; t < 200; t++) {
      let s = ''; for (let i = 0; i < len; i++) s += rng.pick(alphabet);
      if (accepts(m, s)) cands.push(s);
    }
    if (cands.length > 20) break;
  }
  return cands.length ? rng.pick(cands) : null;
}

export { formText };
