// Rewriting into restricted connective sets (functional completeness drills).
import { Not, Bin, V, K, And, Or, Imp, Nand, Nor, show, connectives, equivalent, strip, same } from './prop.js';

// Remove →, ↔, ⊕, ↑, ↓ (leaving ¬, ∧, ∨, T, F).
export function toBasic(n) {
  switch (n.t) {
    case 'not': return Not(toBasic(n.a));
    case 'bin': {
      const a = toBasic(n.a), b = toBasic(n.b);
      switch (n.op) {
        case 'and': return And(a, b);
        case 'or': return Or(a, b);
        case 'imp': return Or(Not(a), b);
        case 'iff': return And(Or(Not(a), b), Or(Not(b), a));
        case 'xor': return Or(And(a, Not(b)), And(Not(a), b));
        case 'nand': return Not(And(a, b));
        case 'nor': return Not(Or(a, b));
      }
    }
  }
  return n;
}

function dn(n) { // remove double negations
  if (n.t === 'not' && n.a.t === 'not') return dn(n.a.a);
  if (n.t === 'not') return Not(dn(n.a));
  if (n.t === 'bin') return Bin(n.op, dn(n.a), dn(n.b));
  return n;
}

// Only ¬ and ∧ : A ∨ B ⇔ ¬(¬A ∧ ¬B)
export function toNotAnd(n) {
  const go = (x) => {
    if (x.t === 'not') return Not(go(x.a));
    if (x.t === 'bin') {
      const a = go(x.a), b = go(x.b);
      if (x.op === 'or') return Not(And(Not(a), Not(b)));
      return Bin(x.op, a, b);
    }
    return x;
  };
  return dn(go(toBasic(n)));
}

// Only ¬ and ∨ : A ∧ B ⇔ ¬(¬A ∨ ¬B)
export function toNotOr(n) {
  const go = (x) => {
    if (x.t === 'not') return Not(go(x.a));
    if (x.t === 'bin') {
      const a = go(x.a), b = go(x.b);
      if (x.op === 'and') return Not(Or(Not(a), Not(b)));
      return Bin(x.op, a, b);
    }
    return x;
  };
  return dn(go(toBasic(n)));
}

// NAND only, from a ¬/∧ formula.
function nandOf(x) {
  if (x.t === 'var') return x;
  if (x.t === 'const') { const p = V('p'); return x.v ? Nand(p, Nand(p, p)) : Nand(Nand(p, Nand(p, p)), Nand(p, Nand(p, p))); }
  if (x.t === 'not') {
    if (x.a.t === 'not') return nandOf(x.a.a);
    if (x.a.t === 'bin' && x.a.op === 'and') return Nand(nandOf(x.a.a), nandOf(x.a.b));
    const y = nandOf(x.a);
    return Nand(y, y);
  }
  if (x.t === 'bin' && x.op === 'and') {
    const m = Nand(nandOf(x.a), nandOf(x.b));
    return Nand(m, m);
  }
  throw new Error('nandOf expects ¬/∧ only');
}
// Same, but keep ¬ in front of variables (the lecturer's middle line).
function nandKeepLits(x) {
  if (x.t === 'var' || x.t === 'const') return x;
  if (x.t === 'not') {
    if (x.a.t === 'not') return nandKeepLits(x.a.a);
    if (x.a.t === 'bin' && x.a.op === 'and') return Nand(nandKeepLits(x.a.a), nandKeepLits(x.a.b));
    if (x.a.t === 'var') return x;
    const y = nandKeepLits(x.a);
    return Not(y);
  }
  if (x.t === 'bin' && x.op === 'and') return Not(Nand(nandKeepLits(x.a), nandKeepLits(x.b)));
  return x;
}

function norOf(x) {
  if (x.t === 'var') return x;
  if (x.t === 'not') {
    if (x.a.t === 'not') return norOf(x.a.a);
    if (x.a.t === 'bin' && x.a.op === 'or') return Nor(norOf(x.a.a), norOf(x.a.b));
    const y = norOf(x.a);
    return Nor(y, y);
  }
  if (x.t === 'bin' && x.op === 'or') { const m = Nor(norOf(x.a), norOf(x.b)); return Nor(m, m); }
  throw new Error('norOf expects ¬/∨ only');
}

function fimpOf(x) { // ¬A = A → F ; A ∨ B = (A → F) → B ; A ∧ B = (A → (B → F)) → F
  if (x.t === 'var') return x;
  if (x.t === 'const') return x.v ? Imp(K(false), K(false)) : K(false);
  if (x.t === 'not') return Imp(fimpOf(x.a), K(false));
  if (x.t === 'bin' && x.op === 'or') return Imp(Imp(fimpOf(x.a), K(false)), fimpOf(x.b));
  if (x.t === 'bin' && x.op === 'and') return Imp(Imp(fimpOf(x.a), Imp(fimpOf(x.b), K(false))), K(false));
  throw new Error('fimpOf expects ¬/∧/∨');
}

export const TARGETS = {
  nand: { label: '↑ (NAND) only', allowed: ['nand'], short: '↑ only' },
  nor: { label: '↓ (NOR) only', allowed: ['nor'], short: '↓ only' },
  notand: { label: '¬ and ∧ only', allowed: ['not', 'and'], short: '¬, ∧' },
  notor: { label: '¬ and ∨ only', allowed: ['not', 'or'], short: '¬, ∨' },
  notandor: { label: '¬, ∧ and ∨ only', allowed: ['not', 'and', 'or'], short: '¬, ∧, ∨' },
  fimp: { label: 'F and → only', allowed: ['imp', 'F'], short: 'F, →' },
};

export function convert(n, target) {
  n = strip(n);
  switch (target) {
    case 'nand': return nandOf(toNotAnd(n));
    case 'nor': return norOf(toNotOr(n));
    case 'notand': return toNotAnd(n);
    case 'notor': return toNotOr(n);
    case 'notandor': return dn(toBasic(n));
    case 'fimp': return fimpOf(dn(toBasic(n)));
  }
  throw new Error('unknown target');
}

// Model solution lines in the lecturer's layout.
export function solutionSteps(n, target) {
  n = strip(n);
  const steps = [{ f: n, why: '' }];
  const push = (f, why) => { if (!same(f, steps[steps.length - 1].f)) steps.push({ f, why }); };
  const basic = dn(toBasic(n));
  const used = [];
  const c = connectives(n);
  if (c.has('imp')) used.push('Conditional');
  if (c.has('iff')) used.push('Bi-conditional, Conditional');
  if (c.has('xor')) used.push('Rule for ⊕');
  if (c.has('nand')) used.push('Rule for NAND');
  if (c.has('nor')) used.push('A ↓ B ⇔ ¬(A ∨ B)');
  push(basic, used.join(', ') + (used.length && !same(basic, toBasic(n)) ? ', Double Negation' : ''));
  if (target === 'nand' || target === 'notand') {
    const na = toNotAnd(n);
    push(na, "De Morgan, Double Negation  (A ∨ B ⇔ ¬(¬A ∧ ¬B))");
    if (target === 'nand') {
      const mid = nandKeepLits(na);
      const fin = nandOf(na);
      if (!same(mid, fin) && connectives(mid).has('nand')) push(mid, '¬(A ∧ B) ⇔ A ↑ B  (Rule for NAND)');
      push(fin, '¬A ⇔ A ↑ A' + (connectives(na).has('and') ? ',  A ∧ B ⇔ (A ↑ B) ↑ (A ↑ B)' : ''));
    }
  } else if (target === 'nor' || target === 'notor') {
    const no = toNotOr(n);
    push(no, "De Morgan, Double Negation  (A ∧ B ⇔ ¬(¬A ∨ ¬B))");
    if (target === 'nor') push(norOf(no), '¬(A ∨ B) ⇔ A ↓ B,  ¬A ⇔ A ↓ A');
  } else if (target === 'fimp') {
    push(fimpOf(basic), '¬A ⇔ A → F,  A ∨ B ⇔ ¬A → B,  A ∧ B ⇔ ¬(A → ¬B)');
  }
  return steps;
}

export function checkRestricted(userAst, original, target) {
  const allowed = new Set(TARGETS[target].allowed);
  const used = connectives(userAst);
  const bad = [...used].filter((c) => !allowed.has(c));
  const eq = equivalent(userAst, original);
  return { allowedOnly: bad.length === 0, bad, equiv: eq.equiv, env: eq.env, ok: bad.length === 0 && eq.equiv };
}

export const OPNAME = { not: '¬', and: '∧', or: '∨', imp: '→', iff: '↔', xor: '⊕', nand: '↑', nor: '↓', T: 'T', F: 'F' };
export { show };
