// English arguments → propositional logic, and the "try to make it false" method
// used in the lecturer's 2023 Test 2 solution.
import { parse, show, V, Not, And, Imp, evaluate, vars, rows, envText, size } from './prop.js';

export const FORMS = [
  { id: 'mp', name: 'Modus ponens', prem: ['a → b', 'a'], concl: 'b', valid: true },
  { id: 'mt', name: 'Modus tollens', prem: ['a → b', '¬b'], concl: '¬a', valid: true },
  { id: 'hs', name: 'Chain of implications', prem: ['a → b', 'b → c'], concl: 'a → c', valid: true },
  { id: 't23', name: '2023 Test 2 pattern', prem: ['¬a → b', 'b → c', '¬a'], concl: 'c', valid: true },
  { id: 'ds', name: 'Disjunctive syllogism', prem: ['a ∨ b', '¬a'], concl: 'b', valid: true },
  { id: 'ac', name: 'Affirming the consequent', prem: ['a → b', 'b'], concl: 'a', valid: false },
  { id: 'da', name: 'Denying the antecedent', prem: ['a → b', '¬a'], concl: '¬b', valid: false },
  { id: 'xo', name: 'Reading “or” as exclusive (PROP4 example)', prem: ['a ∨ b', 'a'], concl: '¬b', valid: false },
  { id: 'cd', name: 'Proof by cases', prem: ['a → c', 'b → c', 'a ∨ b'], concl: 'c', valid: true },
  { id: 'both', name: 'Two consequences', prem: ['a → b', 'a → c', 'a'], concl: 'b ∧ c', valid: true },
  { id: 'iffn', name: 'Biconditional', prem: ['a ↔ b', '¬a'], concl: '¬b', valid: true },
  { id: 'andmt', name: 'Conjunctive antecedent', prem: ['(a ∧ b) → c', 'a', '¬c'], concl: '¬b', valid: true },
  { id: 'orcons', name: 'Disjunctive consequent', prem: ['a → (b ∨ c)', 'a', '¬b'], concl: 'c', valid: true },
  { id: 'twoca', name: 'Two causes', prem: ['a → b', 'c → b', 'b'], concl: 'a ∨ c', valid: false },
  { id: 'halfcd', name: 'Half a dilemma', prem: ['a ∨ b', 'a → c'], concl: 'c', valid: false },
  { id: 'notboth', name: 'Not both', prem: ['¬(a ∧ b)', 'a'], concl: '¬b', valid: true },
  { id: 'eitherway', name: 'Either way', prem: ['a → b', '¬a → c'], concl: 'b ∨ c', valid: true },
  { id: 'chainmt', name: 'Chain, then tollens', prem: ['a → b', 'b → c', '¬c'], concl: '¬a', valid: true },
  { id: 'dsmt', name: 'Eliminate one option', prem: ['a ∨ b', 'b → c', '¬c'], concl: 'a', valid: true },
  { id: 'reverse', name: 'Reversed chain', prem: ['a → b', 'b → c'], concl: 'c → a', valid: false },
];

export const THEMES = [
  { id: 'test', atoms: [
    { l: 't', pos: 'the test is on Thursday', neg: 'the test is not on Thursday' },
    { l: 's', pos: 'I can go shopping', neg: 'I cannot go shopping' },
    { l: 'm', pos: 'I can buy milk', neg: 'I cannot buy milk' }] },
  { id: 'rain', atoms: [
    { l: 'r', pos: 'it rains', neg: 'it does not rain' },
    { l: 'c', pos: 'the match is cancelled', neg: 'the match is not cancelled' },
    { l: 'm', pos: 'we go to the movies', neg: 'we do not go to the movies' }] },
  { id: 'study', atoms: [
    { l: 's', pos: 'I study the induction notes', neg: 'I do not study the induction notes' },
    { l: 'p', pos: 'I pass Test 2', neg: 'I do not pass Test 2' },
    { l: 'c', pos: 'I celebrate', neg: 'I do not celebrate' }] },
  { id: 'server', atoms: [
    { l: 'd', pos: 'the server is down', neg: 'the server is not down' },
    { l: 'w', pos: 'the website loads', neg: 'the website does not load' },
    { l: 'c', pos: 'customers complain', neg: 'customers do not complain' }] },
  { id: 'bus', atoms: [
    { l: 'b', pos: 'the bus is late', neg: 'the bus is not late' },
    { l: 'm', pos: 'I miss the lecture', neg: 'I do not miss the lecture' },
    { l: 'r', pos: 'I read the notes', neg: 'I do not read the notes' }] },
  { id: 'cafe', atoms: [
    { l: 'o', pos: 'the café is open', neg: 'the café is not open' },
    { l: 'c', pos: 'I buy a coffee', neg: 'I do not buy a coffee' },
    { l: 'a', pos: 'I stay awake in class', neg: 'I do not stay awake in class' }] },
  { id: 'socrates', atoms: [
    { l: 'h', pos: 'Socrates is at home', neg: 'Socrates is not at home' },
    { l: 'p', pos: 'Socrates is happy', neg: 'Socrates is not happy' },
    { l: 'w', pos: 'Socrates is writing', neg: 'Socrates is not writing' }] },
  { id: 'lab', atoms: [
    { l: 'l', pos: 'the lab is booked', neg: 'the lab is not booked' },
    { l: 't', pos: 'the tutorial runs', neg: 'the tutorial does not run' },
    { l: 'q', pos: 'we get through the questions', neg: 'we do not get through the questions' }] },
];

const cap = (s) => s.charAt(0).toUpperCase() + s.slice(1);

// English for a premise/conclusion built from a, b, c.
function english(n, atoms, start = true) {
  const C = start ? cap : (x) => x;
  const A = (x) => atoms[x.name];
  const lit = (x) => (x.t === 'var' ? A(x).pos : x.t === 'not' && x.a.t === 'var' ? A(x.a).neg : null);
  const clause = (x) => {
    const l = lit(x);
    if (l) return l;
    if (x.t === 'bin' && x.op === 'and') return `${clause(x.a)} and ${clause(x.b)}`;
    if (x.t === 'bin' && x.op === 'or') return `${clause(x.a)} or ${clause(x.b)}`;
    if (x.t === 'not' && x.a.t === 'bin' && x.a.op === 'and') return `it is not the case that both ${clause(x.a.a)} and ${clause(x.a.b)}`;
    throw new Error('no English for ' + show(x));
  };
  if (n.t === 'bin' && n.op === 'imp') return `${C('if')} ${clause(n.a)}, then ${clause(n.b)}.`;
  if (n.t === 'bin' && n.op === 'iff') return `${C(clause(n.a))} if and only if ${clause(n.b)}.`;
  return C(clause(n)) + '.';
}

const subst = (n, map) => {
  if (n.t === 'var') return V(map[n.name]);
  if (n.t === 'not') return Not(subst(n.a, map));
  if (n.t === 'bin') return { t: 'bin', op: n.op, a: subst(n.a, map), b: subst(n.b, map) };
  return n;
};

export function makeArgument(form, theme, order = [0, 1, 2]) {
  const atomFor = { a: theme.atoms[order[0]], b: theme.atoms[order[1]], c: theme.atoms[order[2]] };
  const used = new Set();
  for (const s of [...form.prem, form.concl]) for (const v of vars(parse(s))) used.add(v);
  const letters = {};
  const meaning = {};
  for (const k of ['a', 'b', 'c']) if (used.has(k)) { letters[k] = atomFor[k].l; meaning[atomFor[k].l] = atomFor[k].pos; }
  const premAst = form.prem.map((s) => subst(parse(s), letters));
  const conclAst = subst(parse(form.concl), letters);
  const premEn = form.prem.map((s) => english(parse(s), atomFor));
  const conclEn = 'Therefore ' + english(parse(form.concl), atomFor, false);
  const wff = Imp(premAst.reduce((acc, x) => (acc ? And(acc, x) : x)), conclAst);
  return {
    form, theme: theme.id, premAst, conclAst, premEn, conclEn, wff, meaning,
    atoms: Object.entries(meaning).map(([l, m]) => ({ l, m })),
    valid: form.valid,
  };
}

// Distractor list for "which are the atomic propositions?"
export function atomChoices(arg, theme) {
  const real = arg.atoms.map((a) => a.m);
  const negs = theme.atoms.filter((a) => real.includes(a.pos)).map((a) => a.neg);
  return { correct: real, distractors: negs };
}

// ---------------------------------------------------------------- falsification
// Three-valued evaluation: true / false / undefined (unknown).
function val(n, as) {
  switch (n.t) {
    case 'var': return as[n.name];
    case 'const': return n.v;
    case 'not': { const a = val(n.a, as); return a === undefined ? undefined : !a; }
    case 'bin': {
      const a = val(n.a, as), b = val(n.b, as);
      switch (n.op) {
        case 'and': if (a === false || b === false) return false; if (a && b) return true; return undefined;
        case 'or': if (a === true || b === true) return true; if (a === false && b === false) return false; return undefined;
        case 'imp': if (a === false || b === true) return true; if (a === true && b === false) return false; return undefined;
        case 'iff': if (a === undefined || b === undefined) return undefined; return a === b;
        case 'xor': if (a === undefined || b === undefined) return undefined; return a !== b;
        case 'nand': if (a === false || b === false) return true; if (a && b) return false; return undefined;
        case 'nor': if (a === true || b === true) return false; if (a === false && b === false) return true; return undefined;
      }
    }
  }
  return undefined;
}

const TF = (b) => (b ? 'T' : 'F');

// Try to make (P1 ∧ … ∧ Pk) → C false. Returns {valid, lines, counterexample}.
export function falsify(premAst, conclAst) {
  const lines = ['For the WFF to be false, every premise must be T and the conclusion must be F.'];
  const all = vars(...premAst, conclAst);
  const prem = premAst.map((f, i) => ({ f, v: true, label: `premise ${i + 1}` }))
    .sort((x, y) => size(x.f) - size(y.f));
  const reqs = [{ f: conclAst, v: false, label: 'the conclusion' }, ...prem];
  const res = run(reqs, {}, lines, 0);
  if (res.contradiction) {
    lines.push('So it is impossible to make the WFF false: it is a tautology, and the argument is valid.');
    return { valid: true, lines };
  }
  const env = { ...res.assign };
  for (const v of all) if (env[v] === undefined) env[v] = false;
  lines.push(`This valuation (${envText(env, all)}) makes every premise T and the conclusion F, so the WFF is not a tautology and the argument is invalid.`);
  return { valid: false, lines, counterexample: env };
}

function evalText(f, as) {
  if (f.t === 'bin') {
    const a = val(f.a, as), b = val(f.b, as), r = val(f, as);
    if (a !== undefined && b !== undefined) return `${show(f)} = ${TF(a)} ${({ and: '∧', or: '∨', imp: '→', iff: '↔', xor: '⊕', nand: '↑', nor: '↓' })[f.op]} ${TF(b)} = ${TF(r)}`;
  }
  if (f.t === 'not') { const a = val(f.a, as); if (a !== undefined) return `${show(f)} = ¬${TF(a)} = ${TF(!a)}`; }
  return `${show(f)} = ${TF(val(f, as))}`;
}

function run(reqs0, assign0, lines, depth) {
  const assign = { ...assign0 };
  const queue = reqs0.map((r) => ({ ...r }));
  const say = (s) => lines.push(s);
  const L = (r) => cap(r.label);
  const add = (r, f, v) => queue.push({ f, v, label: r.label, derived: true });

  // returns true if it made progress at the given level
  function step(level) {
    for (const r of queue) {
      if (r.done) continue;
      const f = r.f, v = r.v;
      if (level === 1) {
        if (f.t === 'var') {
          assign[f.name] = v; r.done = true;
          if (!r.derived) say(`${L(r)}: ${f.name} = ${TF(v)}.`);
          return true;
        }
        if (f.t === 'not') {
          r.done = true; add(r, f.a, !v);
          say(`${L(r)}: ${show(f)} = ${TF(v)}, so ${show(f.a)} = ${TF(!v)}.`);
          return true;
        }
        if (f.t === 'bin' && ((f.op === 'and' && v) || (f.op === 'or' && !v) || (f.op === 'imp' && !v) || (f.op === 'nand' && !v) || (f.op === 'nor' && v))) {
          r.done = true;
          const [va, vb] = f.op === 'and' ? [true, true] : f.op === 'or' ? [false, false] : f.op === 'imp' ? [true, false] : f.op === 'nand' ? [true, true] : [false, false];
          add(r, f.a, va); add(r, f.b, vb);
          say(`${L(r)}: ${show(f)} = ${TF(v)}, so ${show(f.a)} = ${TF(va)} and ${show(f.b)} = ${TF(vb)}.`);
          return true;
        }
        continue;
      }
      if (f.t !== 'bin') continue;
      const a = val(f.a, assign), b = val(f.b, assign);
      const derive = (g, w, known, kv) => {
        r.done = true; add(r, g, w);
        say(`${L(r)}: ${show(f)} = ${TF(v)} and ${show(known)} = ${TF(kv)}, so ${show(g)} = ${TF(w)}.`);
        return true;
      };
      if (level === 2) {
        if (f.op === 'imp' && v && a === true) return derive(f.b, true, f.a, true);
        if (f.op === 'or' && v && a === false) return derive(f.b, true, f.a, false);
        if (f.op === 'or' && v && b === false) return derive(f.a, true, f.b, false);
        if (f.op === 'and' && !v && a === true) return derive(f.b, false, f.a, true);
        if (f.op === 'and' && !v && b === true) return derive(f.a, false, f.b, true);
        if ((f.op === 'iff' || f.op === 'xor') && a !== undefined) return derive(f.b, (f.op === 'iff') === v ? a : !a, f.a, a);
        if ((f.op === 'iff' || f.op === 'xor') && b !== undefined) return derive(f.a, (f.op === 'iff') === v ? b : !b, f.b, b);
      }
      if (level === 3) {
        if (f.op === 'imp' && v && b === false) return derive(f.a, false, f.b, false);
      }
    }
    return false;
  }

  let guard = 0;
  while (guard++ < 300) {
    for (const r of queue) {
      if (r.done) continue;
      const known = val(r.f, assign);
      if (known === undefined) continue;
      r.done = true;
      if (known !== r.v) {
        say(`${L(r)}: but ${evalText(r.f, assign)}, not ${TF(r.v)}. Contradiction.`);
        return { contradiction: true };
      }
    }
    if (!(step(1) || step(2) || step(3))) break;
  }
  const pending = queue.filter((r) => !r.done);
  if (!pending.length) return { contradiction: false, assign };
  const free = vars(...pending.map((r) => r.f)).filter((x) => assign[x] === undefined);
  if (!free.length || depth > 3) return { contradiction: false, assign };
  const x = free[0];
  const linesT = [], linesF = [];
  const rT = run(pending, { ...assign, [x]: true }, linesT, depth + 1);
  lines.push(`Nothing more is forced, so try both values of ${x}.`);
  lines.push(`Case ${x} = T: ` + (linesT.join(' ') || 'no contradiction.'));
  if (!rT.contradiction) return { contradiction: false, assign: { ...rT.assign, [x]: true } };
  const rF = run(pending, { ...assign, [x]: false }, linesF, depth + 1);
  lines.push(`Case ${x} = F: ` + (linesF.join(' ') || 'no contradiction.'));
  if (!rF.contradiction) return { contradiction: false, assign: { ...rF.assign, [x]: false } };
  return { contradiction: true };
}

// Truth-table check of validity (premises ∧ … → conclusion).
export function validity(premAst, conclAst) {
  const vs = vars(...premAst, conclAst);
  for (const env of rows(vs)) {
    if (premAst.every((p) => evaluate(p, env)) && !evaluate(conclAst, env)) return { valid: false, env, vs };
  }
  return { valid: true, vs };
}
