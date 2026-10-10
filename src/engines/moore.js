// Moore machines as defined in Tutorial 5: δ maps into Q \ {q0}, g : Q \ {q0} → X,
// and each input letter is overwritten by g of the state entered.

export function runMoore(m, w) {
  const path = [m.start];
  let q = m.start;
  let out = '';
  for (const c of w) {
    const nx = m.delta[q]?.[c];
    if (nx == null) return { path, out, stuck: true };
    q = nx; path.push(q); out += m.g[q];
  }
  return { path, out };
}

export function validateMoore(m, alphabet) {
  const errs = [];
  for (const q of m.states) for (const a of alphabet) {
    const t = m.delta[q]?.[a];
    if (t == null || t === '') errs.push(`δ(${q}, ${a}) is missing.`);
    else if (!m.states.includes(t)) errs.push(`δ(${q}, ${a}) = ${t} isn't a state.`);
    else if (t === m.start) errs.push(`δ(${q}, ${a}) = ${m.start}: a Moore machine (as defined in tutorial 5) can never move back into ${m.start}.`);
  }
  for (const q of m.states) if (q !== m.start && (m.g[q] == null || m.g[q] === '' || !alphabet.includes(m.g[q]))) errs.push(`g(${q}) must be one of ${alphabet.join(', ')}.`);
  return errs;
}

export const TUT5 = {
  states: ['q0', 'q1', 'q2', 'q3'], start: 'q0',
  delta: { q0: { 0: 'q1', 1: 'q2' }, q1: { 0: 'q1', 1: 'q2' }, q2: { 0: 'q3', 1: 'q1' }, q3: { 0: 'q3', 1: 'q1' } },
  g: { q1: '0', q2: '1', q3: '0' },
};

// Target behaviours for design drills: f maps an input string to the wanted output.
export const MOORE_TARGETS = [
  { id: 'swap', title: 'Swap the digits', desc: 'Every 0 becomes 1 and every 1 becomes 0 (11010 → 00101). Tutorial 5 Q2(b).', f: (w) => [...w].map((c) => (c === '0' ? '1' : '0')).join(''), hint: 'Two states besides q0 are enough: one entered on reading 0 (outputs 1), one entered on reading 1 (outputs 0).' },
  { id: 'copy', title: 'Copy the input', desc: 'The output equals the input (0110 → 0110).', f: (w) => w, hint: 'Enter a state that outputs whatever was just read.' },
  { id: 'zero', title: 'Blank it out', desc: 'Every letter is overwritten by 0 (1011 → 0000).', f: (w) => '0'.repeat(w.length), hint: 'One state besides q0 is enough.' },
  { id: 'delay', title: 'Delay by one', desc: 'Output the previous input letter, with 0 at the start (1101 → 0110).', f: (w) => (w.length ? '0' + w.slice(0, -1) : ''), hint: 'Remember the letter just read in the state, and output the one before it.' },
  { id: 'parity', title: 'Running parity', desc: 'Output 1 exactly when the input so far contains an odd number of 1s (1101 → 1001).', f: (w) => { let p = 0; return [...w].map((c) => { if (c === '1') p ^= 1; return String(p); }).join(''); }, hint: 'Two states: “even so far” (outputs 0) and “odd so far” (outputs 1).' },
  { id: 'repeat', title: 'Spot a repeat', desc: 'Output 1 when the letter read equals the previous letter, otherwise 0; the first output is 0 (0010 → 0100).', f: (w) => [...w].map((c, i) => (i > 0 && w[i - 1] === c ? '1' : '0')).join(''), hint: 'States need to remember the last letter and whether it repeated: four states besides q0.' },
];

export function checkMooreDesign(m, target, alphabet = ['0', '1'], maxLen = 7) {
  const errs = validateMoore(m, alphabet);
  if (errs.length) return { ok: false, message: errs[0] };
  const rec = (s) => {
    if (s.length > maxLen) return null;
    const r = runMoore(m, s);
    if (r.out !== target.f(s)) return { w: s, got: r.out, want: target.f(s), path: r.path };
    for (const a of alphabet) { const x = rec(s + a); if (x) return x; }
    return null;
  };
  // breadth-first so the counterexample is short
  for (let len = 1; len <= maxLen; len++) {
    const strs = [''];
    for (let i = 0; i < len; i++) { const nx = []; for (const s of strs) for (const a of alphabet) nx.push(s + a); strs.splice(0, strs.length, ...nx); }
    for (const s of strs) {
      const r = runMoore(m, s);
      if (r.out !== target.f(s)) return { ok: false, w: s, got: r.out, want: target.f(s), path: r.path, message: `On input ${s} your machine outputs ${r.out}, but it should output ${target.f(s)}.` };
    }
  }
  return { ok: true, message: `Correct on every input up to length ${maxLen}.` };
}

export function randomMoore(rng, n = rng.pick([3, 4])) {
  const states = Array.from({ length: n }, (_, i) => 'q' + i);
  for (let t = 0; t < 200; t++) {
    const delta = {};
    for (const q of states) delta[q] = { 0: rng.pick(states.slice(1)), 1: rng.pick(states.slice(1)) };
    const g = {};
    for (const q of states.slice(1)) g[q] = rng.pick(['0', '1']);
    if (new Set(Object.values(g)).size < 2) continue;
    // all states reachable
    const seen = new Set(['q0']); const st = ['q0'];
    while (st.length) { const q = st.pop(); for (const a of ['0', '1']) { const r = delta[q][a]; if (!seen.has(r)) { seen.add(r); st.push(r); } } }
    if (seen.size !== n) continue;
    return { states, start: 'q0', delta, g };
  }
  return TUT5;
}
