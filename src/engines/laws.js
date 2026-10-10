// The supplied "Laws of Logical Equivalence" sheet, as rewrite rules, plus a step checker
// for law-by-law equivalence proofs.
import {
  Not, Bin, K, key, same, positions, at, replaceAt, equivalent, strip, show, envText, vars,
} from './prop.js';

const M = (name) => ({ t: 'meta', name });
const A = M('A'), B = M('B'), C = M('C');
const and = (x, y) => Bin('and', x, y), or = (x, y) => Bin('or', x, y);
const imp = (x, y) => Bin('imp', x, y), iff = (x, y) => Bin('iff', x, y);
const xor = (x, y) => Bin('xor', x, y), nand = (x, y) => Bin('nand', x, y), nor = (x, y) => Bin('nor', x, y);
const not = Not, T = K(true), F = K(false);

export const LAWS = [
  { id: 'idem', n: 1, name: 'Idempotence', forms: [[and(A, A), A], [or(A, A), A]], lenient: true },
  { id: 'comm', n: 2, name: 'Commutativity', forms: [[and(A, B), and(B, A)], [or(A, B), or(B, A)]] },
  { id: 'assoc', n: 3, name: 'Associativity', forms: [[and(A, and(B, C)), and(and(A, B), C)], [or(A, or(B, C)), or(or(A, B), C)]] },
  { id: 'dist', n: 4, name: 'Distributivity', forms: [[and(A, or(B, C)), or(and(A, B), and(A, C))], [or(A, and(B, C)), and(or(A, B), or(A, C))]], lenient: true },
  { id: 'demorgan', n: 5, name: "De Morgan's Laws", forms: [[not(and(A, B)), or(not(A), not(B))], [not(or(A, B)), and(not(A), not(B))]] },
  { id: 'dneg', n: 6, name: 'Double Negation', forms: [[not(not(A)), A]] },
  { id: 'excl', n: 7, name: 'Excluded Middle', forms: [[and(A, not(A)), F], [or(A, not(A)), T]], lenient: true },
  { id: 'ident', n: 8, name: 'Identity', forms: [[and(A, T), A], [or(A, F), A]], lenient: true },
  { id: 'dom', n: 9, name: 'Domination', forms: [[and(A, F), F], [or(A, T), T]], lenient: true },
  { id: 'cond', n: 10, name: 'Conditional', forms: [[imp(A, B), or(not(A), B)]] },
  { id: 'bicond', n: 11, name: 'Bi-conditional', forms: [[iff(A, B), and(imp(A, B), imp(B, A))]] },
  { id: 'xor', n: 12, name: 'Rule for ⊕', forms: [[xor(A, B), or(and(A, not(B)), and(not(A), B))]] },
  { id: 'nand', n: 13, name: 'Rule for NAND', forms: [[nand(A, B), not(and(A, B))]] },
  { id: 'nor', n: 14, name: 'Rule for NOR', forms: [[nor(A, B), not(or(A, B))]], extra: true },
];
export const LAW = Object.fromEntries(LAWS.map((l) => [l.id, l]));

// The sheet's own wording, for the reference panel.
export const LAW_SHEET = [
  ['Idempotence', ['A ∧ A ⇔ A', 'A ∨ A ⇔ A']],
  ['Commutativity', ['A ∧ B ⇔ B ∧ A', 'A ∨ B ⇔ B ∨ A']],
  ['Associativity', ['A ∧ (B ∧ C) ⇔ (A ∧ B) ∧ C', 'A ∨ (B ∨ C) ⇔ (A ∨ B) ∨ C']],
  ['Distributivity', ['A ∧ (B ∨ C) ⇔ (A ∧ B) ∨ (A ∧ C)', 'A ∨ (B ∧ C) ⇔ (A ∨ B) ∧ (A ∨ C)']],
  ["De Morgan's Laws", ['¬(A ∧ B) ⇔ ¬A ∨ ¬B', '¬(A ∨ B) ⇔ ¬A ∧ ¬B']],
  ['Double Negation', ['¬¬A ⇔ A']],
  ['Excluded Middle', ['A ∧ ¬A ⇔ false', 'A ∨ ¬A ⇔ true']],
  ['Identity', ['A ∧ true ⇔ A', 'A ∨ false ⇔ A']],
  ['Domination', ['A ∧ false ⇔ false', 'A ∨ true ⇔ true']],
  ['Conditional', ['A → B ⇔ ¬A ∨ B']],
  ['Bi-conditional', ['A ↔ B ⇔ (A → B) ∧ (B → A)']],
  ['Rule for ⊕', ['A ⊕ B ⇔ (A ∧ ¬B) ∨ (¬A ∧ B)']],
  ['Rule for NAND', ['A ↑ B ⇔ ¬(A ∧ B)']],
];

// ---------------------------------------------------------------- matching
// Returns every way pattern p matches node n: [{b: bindings, comm: bool}]
function matchAll(p, n, b, lenient) {
  if (p.t === 'meta') {
    if (b[p.name]) return same(b[p.name], n) ? [{ b, comm: false }] : [];
    return [{ b: { ...b, [p.name]: n }, comm: false }];
  }
  if (p.t !== n.t) return [];
  if (p.t === 'var') return p.name === n.name ? [{ b, comm: false }] : [];
  if (p.t === 'const') return p.v === n.v ? [{ b, comm: false }] : [];
  if (p.t === 'not') return matchAll(p.a, n.a, b, lenient);
  if (p.op !== n.op) return [];
  const out = [];
  for (const r1 of matchAll(p.a, n.a, b, lenient)) {
    for (const r2 of matchAll(p.b, n.b, r1.b, lenient)) out.push({ b: r2.b, comm: r1.comm || r2.comm });
  }
  if (lenient && (p.op === 'and' || p.op === 'or') && !same(n.a, n.b)) {
    for (const r1 of matchAll(p.a, n.b, b, lenient)) {
      for (const r2 of matchAll(p.b, n.a, r1.b, lenient)) out.push({ b: r2.b, comm: true });
    }
  }
  return out;
}

function metasOf(p, acc = new Set()) {
  if (p.t === 'meta') acc.add(p.name);
  if (p.t === 'not') metasOf(p.a, acc);
  if (p.t === 'bin') { metasOf(p.a, acc); metasOf(p.b, acc); }
  return acc;
}

function inst(p, b) {
  if (p.t === 'meta') return b[p.name];
  if (p.t === 'not') return Not(inst(p.a, b));
  if (p.t === 'bin') return Bin(p.op, inst(p.a, b), inst(p.b, b));
  return p;
}

// All single applications of one law (both directions) anywhere in ast.
export function rewrites(ast, law, { lenient = false, onlyPath = null, bfs = false } = {}) {
  const out = [];
  const paths = onlyPath ? [onlyPath] : positions(ast);
  const len = lenient && law.lenient;
  for (const path of paths) {
    const node = at(ast, path);
    law.forms.forEach(([L, R], fi) => {
      for (const [from, to, dir] of [[L, R, 'ltr'], [R, L, 'rtl']]) {
        // A bare metavariable matches everything; in searches those uses are found from the other side.
        if (bfs && from.t === 'meta') continue;
        const need = metasOf(to);
        for (const m of matchAll(from, node, {}, len)) {
          if ([...need].some((x) => !m.b[x])) continue;
          const sub = inst(to, m.b);
          if (same(sub, node)) continue;
          out.push({ path, result: replaceAt(ast, path, sub), law: law.id, form: fi, dir, comm: m.comm, before: node, after: sub });
        }
      }
    });
  }
  return out;
}

function neighbours(ast, laws, lenient) {
  const out = [];
  for (const l of laws) for (const r of rewrites(ast, l, { lenient, bfs: true })) out.push(r);
  return out;
}

// Breadth-first search over law applications. Returns Map key -> {depth, comm}
function reach(start, laws, depth, lenient, cap = 4000) {
  const seen = new Map([[key(start), { depth: 0, comm: false, ast: start }]]);
  let frontier = [{ ast: start, comm: false }];
  for (let d = 1; d <= depth; d++) {
    const nextF = [];
    for (const f of frontier) {
      for (const r of neighbours(f.ast, laws, lenient)) {
        const k = key(r.result);
        if (!seen.has(k)) {
          const rec = { depth: d, comm: f.comm || r.comm, ast: r.result };
          seen.set(k, rec);
          nextF.push(rec);
          if (seen.size > cap) return seen;
        }
      }
    }
    frontier = nextF;
  }
  return seen;
}

function connects(prev, next, laws, maxApps, lenient) {
  const kn = key(next);
  const fromPrev = reach(prev, laws, maxApps, lenient);
  if (fromPrev.has(kn)) return { ok: true, apps: fromPrev.get(kn).depth, comm: fromPrev.get(kn).comm };
  // meet in the middle (handles right-to-left uses that introduce new subformulas)
  const fromNext = reach(next, laws, maxApps, lenient);
  let best = null;
  for (const [k, rec] of fromNext) {
    const p = fromPrev.get(k);
    if (p && p.depth + rec.depth <= maxApps) {
      const cand = { ok: true, apps: p.depth + rec.depth, comm: p.comm || rec.comm };
      if (!best || cand.apps < best.apps) best = cand;
    }
  }
  return best || { ok: false };
}

// Check one line of a proof: prev ⇔ next justified by the cited laws.
export function checkStep(prev, next, lawIds, { maxApps = 3 } = {}) {
  prev = strip(prev); next = strip(next);
  if (same(prev, next)) return { ok: false, kind: 'nochange', message: 'This line is identical to the previous one.' };
  const eq = equivalent(prev, next);
  const laws = lawIds.map((id) => LAW[id]).filter(Boolean);
  if (!eq.equiv) {
    const vs = vars(prev, next);
    return {
      ok: false, kind: 'notequiv',
      message: `These two formulas are not logically equivalent: with ${envText(eq.env, vs)} the previous line is ${eq.a ? 'T' : 'F'} but this line is ${eq.b ? 'T' : 'F'}.`,
      env: eq.env,
    };
  }
  if (!laws.length) {
    const sug = suggestLaws(prev, next, maxApps);
    return { ok: false, kind: 'nolaw', message: 'Equivalent, but you need to quote the law you used.' + (sug ? ` (It works with ${sug.names}.)` : ''), suggestion: sug };
  }
  // quote only the laws actually used: drop any cited law the step works without
  const overcited = (lenient) => {
    if (laws.length < 2) return null;
    let keep = [...laws];
    for (const l of laws) {
      const fewer = keep.filter((x) => x !== l);
      if (fewer.length && connects(prev, next, fewer, maxApps, lenient).ok) keep = fewer;
    }
    return keep.length < laws.length ? keep : null;
  };
  const strict = connects(prev, next, laws, maxApps, false);
  if (strict.ok) {
    const keep = overcited(false);
    if (keep) return { ok: false, kind: 'overcite', message: `That line is right, but quote only the law${keep.length > 1 ? 's' : ''} you used: ${keep.map((l) => l.name).join(' + ')}.`, suggestion: { ids: keep.map((l) => l.id), names: keep.map((l) => l.name).join(' + ') } };
    return { ok: true, strict: true, apps: strict.apps, message: okMessage(laws, strict.apps) };
  }
  const len = connects(prev, next, laws, maxApps, true);
  if (len.ok) {
    const keep = overcited(true);
    if (keep) return { ok: false, kind: 'overcite', message: `That line is right, but quote only the law${keep.length > 1 ? 's' : ''} you used: ${keep.map((l) => l.name).join(' + ')}.`, suggestion: { ids: keep.map((l) => l.id), names: keep.map((l) => l.name).join(' + ') } };
    return {
      ok: true, strict: false, apps: len.apps,
      message: okMessage(laws, len.apps) + ' Strictly the sheet\'s pattern has the operands the other way round, so this also uses Commutativity. The lecturer\'s own solutions accept this.',
    };
  }
  const sug = suggestLaws(prev, next, maxApps);
  return {
    ok: false, kind: 'wronglaw',
    message: `The two lines are equivalent, but not by ${laws.map((l) => l.name).join(' + ')} alone.` + (sug ? ` Try ${sug.names}.` : ' It probably needs more than one step.'),
    suggestion: sug,
  };
}

function okMessage(laws, apps) {
  return `Correct use of ${laws.map((l) => l.name).join(' + ')}` + (apps > 1 ? ` (applied ${apps} times in one line).` : '.');
}

// Find the smallest set of laws (1 or 2) that justifies a step.
export function suggestLaws(prev, next, maxApps = 3) {
  for (const l of LAWS) {
    if (l.extra) continue;
    const r = connects(prev, next, [l], maxApps, true);
    if (r.ok) return { ids: [l.id], names: l.name };
  }
  for (let i = 0; i < LAWS.length; i++) for (let j = i + 1; j < LAWS.length; j++) {
    const l1 = LAWS[i], l2 = LAWS[j];
    if (l1.extra || l2.extra) continue;
    const r = connects(prev, next, [l1, l2], Math.min(maxApps, 3), true);
    if (r.ok) return { ids: [l1.id, l2.id], names: `${l1.name} + ${l2.name}` };
  }
  return null;
}

// Rewrites available at one selected subformula (for the click-to-apply mode).
export function optionsAt(ast, path) {
  const out = [];
  for (const law of LAWS) {
    for (const r of rewrites(ast, law, { lenient: true, onlyPath: path })) {
      if (out.some((o) => same(o.result, r.result) && o.law === r.law)) continue;
      out.push({ ...r, lawName: law.name, preview: show(r.after) });
    }
  }
  return out;
}

export function lawName(id) { return LAW[id]?.name ?? id; }

// Recognise law names typed by a student ("demorgan, double neg", "cond.", "DM") .
export function parseLawList(text) {
  const t = (text || '').toLowerCase();
  const found = [];
  const pats = [
    ['idem', /idem/], ['comm', /comm/], ['assoc', /assoc/], ['dist', /distrib|dist\b/],
    ['demorgan', /de ?morgan|\bdm\b/], ['dneg', /double|dneg|¬¬/], ['excl', /excluded|middle/],
    ['ident', /identity|ident/], ['dom', /dominat|\bdom\b/], ['bicond', /bi-?cond|bicon/],
    ['cond', /(^|[^i-])cond(itional)?\b|implication/], ['xor', /⊕|xor|exclusive/], ['nand', /nand|↑/], ['nor', /\bnor\b|↓/],
  ];
  for (const [id, re] of pats) if (re.test(t)) found.push(id);
  // "bi-conditional" also matches the conditional pattern on some spellings; keep both only if both named
  if (found.includes('bicond') && found.includes('cond') && !/(^|[\s,;+&(])cond/.test(t.replace(/bi-?cond(itional)?/g, ''))) {
    found.splice(found.indexOf('cond'), 1);
  }
  return found;
}
