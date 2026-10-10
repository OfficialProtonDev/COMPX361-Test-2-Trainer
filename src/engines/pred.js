// Predicate logic engine: parse quantified formulas, print them in the lecturer's style,
// evaluate on finite worlds and compare two formulas on every small world.
import { SYM } from './prop.js';

export class PredParseError extends Error { constructor(m, pos) { super(m); this.pos = pos; } }

const CHARS = {
  '∀': 'all', '∃': 'ex', '∈': 'in', ':': 'colon', '.': 'colon', '(': 'lp', ')': 'rp', '[': 'lp', ']': 'rp', ',': 'comma',
  '=': 'eq', '≠': 'neq', '¬': 'not', '~': 'not', '!': 'not', '∧': 'and', '&': 'and', '^': 'and', '∨': 'or', '|': 'or',
  '→': 'imp', '↔': 'iff', '⊕': 'xor', '⇒': 'BADIMP', '⇔': 'BADIFF', '-': 'not',
};
const WORDS = { forall: 'all', all: 'all', exists: 'ex', some: 'ex', in: 'in', and: 'and', or: 'or', not: 'not', implies: 'imp', iff: 'iff', xor: 'xor' };
const DOMS = { 'ℝ': 'ℝ', 'ℕ': 'ℕ', 'ℤ': 'ℤ', 'ℂ': 'ℂ', 'ℚ': 'ℚ' };

export function tokenize(s) {
  const out = [];
  let i = 0;
  while (i < s.length) {
    const c = s[i];
    if (/\s/.test(c)) { i++; continue; }
    if (s.startsWith('<->', i)) { out.push({ type: 'iff', pos: i, text: '<->' }); i += 3; continue; }
    if (s.startsWith('->', i)) { out.push({ type: 'imp', pos: i, text: '->' }); i += 2; continue; }
    if (s.startsWith('!=', i) || s.startsWith('=/=', i)) { const L = s.startsWith('!=', i) ? 2 : 3; out.push({ type: 'neq', pos: i, text: '≠' }); i += L; continue; }
    if (s.startsWith('/\\', i)) { out.push({ type: 'and', pos: i, text: '∧' }); i += 2; continue; }
    if (s.startsWith('\\/', i)) { out.push({ type: 'or', pos: i, text: '∨' }); i += 2; continue; }
    if (DOMS[c]) { out.push({ type: 'dom', pos: i, text: DOMS[c] }); i++; continue; }
    if (/[A-Za-z]/.test(c)) {
      const m = /^[A-Za-z]+/.exec(s.slice(i))[0];
      const lw = m.toLowerCase();
      if (m.length > 1 && WORDS[lw]) { out.push({ type: WORDS[lw], pos: i, text: m }); i += m.length; continue; }
      if (/[A-Z]/.test(c)) {
        // predicate symbol (followed by '(') or a domain / set name
        let j = i + 1;
        while (j < s.length && /[A-Za-z0-9_']/.test(s[j])) j++;
        const name = s.slice(i, j);
        let k = j; while (k < s.length && /\s/.test(s[k])) k++;
        if (s[k] === '(') out.push({ type: 'pred', pos: i, text: name });
        else if (name === 'T' || name === 'F') out.push({ type: name, pos: i, text: name });
        else out.push({ type: 'dom', pos: i, text: name });
        i = j; continue;
      }
      const vm = /^[a-z](?:_?\d+|'+)?/.exec(s.slice(i))[0];
      out.push({ type: 'var', pos: i, text: vm.replace('_', '') });
      i += vm.length; continue;
    }
    if (/[0-9]/.test(c)) { const m = /^[0-9]+/.exec(s.slice(i))[0]; out.push({ type: 'num', pos: i, text: m }); i += m.length; continue; }
    if (CHARS[c]) { out.push({ type: CHARS[c], pos: i, text: c }); i++; continue; }
    throw new PredParseError(`Unexpected character “${c}”.`, i);
  }
  out.push({ type: 'eof', pos: s.length, text: '' });
  for (let j = 1; j < out.length; j++) {
    if (out[j].type === 'var' && out[j].text === 'v' && ['var', 'num', 'rp', 'T', 'F'].includes(out[j - 1].type)) out[j] = { ...out[j], type: 'or' };
  }
  return out;
}

const LEVELS = [['iff'], ['imp'], ['xor'], ['or'], ['and']];

export function parsePred(src) {
  if (!src || !src.trim()) throw new PredParseError('Type a formula first.', 0);
  const toks = tokenize(src);
  let k = 0;
  const peek = () => toks[k], next = () => toks[k++];
  const expect = (type, msg) => { if (peek().type !== type) throw new PredParseError(msg, peek().pos); return next(); };

  function level(i) {
    if (i >= LEVELS.length) return unary();
    let left = level(i + 1);
    while (LEVELS[i].includes(peek().type)) {
      const op = next().type;
      const right = level(i + 1);
      left = { t: 'bin', op, a: left, b: right };
    }
    return left;
  }
  function term() {
    const t = peek();
    if (t.type === 'var' || t.type === 'num') { next(); return t.text; }
    throw new PredParseError(`Expected a variable here, found “${t.text || 'the end'}”.`, t.pos);
  }
  function unary() {
    const t = peek();
    if (t.type === 'not') { next(); return { t: 'not', a: unary() }; }
    if (t.type === 'all' || t.type === 'ex') {
      next();
      const v = peek();
      if (v.type !== 'var') throw new PredParseError(`${t.type === 'all' ? '∀' : '∃'} must be followed by a variable such as x.`, v.pos);
      next();
      let dom = null;
      if (peek().type === 'in') {
        next();
        const d = peek();
        if (d.type !== 'dom') throw new PredParseError('Expected a set name after ∈ (for example X or ℝ).', d.pos);
        next(); dom = d.text;
      }
      if (peek().type === 'colon') next();
      if (peek().type === 'eof') throw new PredParseError('The quantifier needs a formula after it.', peek().pos);
      const body = level(0);
      return { t: 'q', q: t.type, v: v.text, dom, body };
    }
    if (t.type === 'lp') {
      next();
      const e = level(0);
      expect('rp', 'Missing a closing bracket.');
      return e;
    }
    if (t.type === 'pred') {
      next();
      expect('lp', 'Expected “(” after the predicate name.');
      const args = [term()];
      while (peek().type === 'comma') { next(); args.push(term()); }
      expect('rp', 'Missing “)” after the predicate arguments.');
      return { t: 'atom', p: t.text, args };
    }
    if (t.type === 'var' || t.type === 'num') {
      const a = term();
      const op = peek();
      if (op.type !== 'eq' && op.type !== 'neq') throw new PredParseError(`A variable on its own isn't a formula. Did you mean P(${a}, …) or ${a} = …?`, op.pos);
      next();
      const b = term();
      const e = { t: 'eq', a, b };
      return op.type === 'neq' ? { t: 'not', a: e } : e;
    }
    if (t.type === 'T' || t.type === 'F') { next(); return { t: 'const', v: t.type === 'T' }; }
    if (t.type === 'BADIMP') throw new PredParseError('Use → inside formulas (⇒ is for logical consequence).', t.pos);
    if (t.type === 'BADIFF') throw new PredParseError('Use ↔ inside formulas (⇔ is for logical equivalence).', t.pos);
    if (t.type === 'dom') throw new PredParseError(`“${t.text}” looks like a predicate: add its arguments, like ${t.text}(x, y).`, t.pos);
    if (t.type === 'eof') throw new PredParseError('The formula ends too early.', t.pos);
    throw new PredParseError(`Unexpected “${t.text}”.`, t.pos);
  }
  const e = level(0);
  if (peek().type !== 'eof') {
    const t = peek();
    if (t.type === 'rp') throw new PredParseError('Too many closing brackets.', t.pos);
    throw new PredParseError(`Missing a connective before “${t.text}”.`, t.pos);
  }
  return e;
}

export function tryParsePred(src) {
  try { return { ok: true, ast: parsePred(src) }; } catch (e) { return { ok: false, error: e.message, pos: e.pos ?? 0 }; }
}

// ---------------------------------------------------------------- printing
const QS = { all: '∀', ex: '∃' };
export function showPred(n) {
  if (n.t === 'q' || (n.t === 'not' && isQChain(n.a))) {
    const parts = [];
    let x = n;
    while (x.t === 'q' || (x.t === 'not' && isQChain(x.a))) {
      if (x.t === 'not') { parts.push('¬'); x = x.a; continue; }
      parts.push(QS[x.q] + x.v + (x.dom ? ' ∈ ' + x.dom : ''));
      x = x.body;
    }
    let s = '';
    parts.forEach((p, i) => { s += p; if (p !== '¬' && i < parts.length - 1) s += ' '; });
    return s + ' : ' + showPred(x);
  }
  switch (n.t) {
    case 'atom': return `${n.p}(${n.args.join(', ')})`;
    case 'eq': return `${n.a} = ${n.b}`;
    case 'const': return n.v ? 'T' : 'F';
    case 'not':
      if (n.a.t === 'eq') return `${n.a.a} ≠ ${n.a.b}`;
      return '¬' + (n.a.t === 'bin' ? '(' + showPred(n.a) + ')' : showPred(n.a));
    case 'bin': {
      const w = (c, side) => {
        if (c.t === 'q' || (c.t === 'not' && isQChain(c.a))) return '(' + showPred(c) + ')';
        if (c.t === 'not' && c.a.t === 'eq') return '(' + showPred(c) + ')';
        if (c.t === 'eq') return '(' + showPred(c) + ')';
        if (c.t === 'bin' && !(c.op === n.op && side === 'L' && (n.op === 'and' || n.op === 'or'))) return '(' + showPred(c) + ')';
        return showPred(c);
      };
      return w(n.a, 'L') + ' ' + SYM[n.op] + ' ' + w(n.b, 'R');
    }
  }
  return '?';
}
function isQChain(n) { return n.t === 'q' || (n.t === 'not' && isQChain(n.a)); }

export function keyPred(n) {
  switch (n.t) {
    case 'q': return QS[n.q] + n.v + (n.dom ? '∈' + n.dom : '') + '[' + keyPred(n.body) + ']';
    case 'atom': return n.p + '(' + n.args.join(',') + ')';
    case 'eq': return n.a + '=' + n.b;
    case 'const': return n.v ? 'T' : 'F';
    case 'not': return '¬' + keyPred(n.a);
    case 'bin': return '(' + keyPred(n.a) + SYM[n.op] + keyPred(n.b) + ')';
  }
  return '?';
}

// ---------------------------------------------------------------- typing & evaluation
// sig: { sorts: ['X','Y'], preds: { P: ['X','Y'] }, domAlias: { X:'X', Dogs:'X' } }
export function freeVars(n, bound = new Set(), acc = []) {
  switch (n.t) {
    case 'q': { const b = new Set(bound); b.add(n.v); freeVars(n.body, b, acc); break; }
    case 'atom': for (const a of n.args) if (/^[a-z]/.test(a) && !bound.has(a) && !acc.includes(a)) acc.push(a); break;
    case 'eq': for (const a of [n.a, n.b]) if (/^[a-z]/.test(a) && !bound.has(a) && !acc.includes(a)) acc.push(a); break;
    case 'not': freeVars(n.a, bound, acc); break;
    case 'bin': freeVars(n.a, bound, acc); freeVars(n.b, bound, acc); break;
  }
  return acc;
}

export function closure(n) {
  const fv = freeVars(n);
  let x = n;
  for (let i = fv.length - 1; i >= 0; i--) x = { t: 'q', q: 'all', v: fv[i], dom: null, body: x };
  return { ast: x, free: fv };
}

class TypeErr extends Error {}

// Assign a sort to each quantifier (stored in a WeakMap) by looking at where its variable is used.
function typeCheck(n, sig) {
  const sortOf = new WeakMap();
  const errors = [];
  function usage(body, v, acc) { // collect sorts of positions where v (free in body) occurs
    switch (body.t) {
      case 'q': if (body.v !== v) usage(body.body, v, acc); break;
      case 'atom': {
        const ps = sig.preds[body.p];
        if (!ps) { errors.push(`There is no predicate called ${body.p} here. Use ${Object.keys(sig.preds).join(' or ')}.`); break; }
        if (ps.length !== body.args.length) { errors.push(`${body.p} takes ${ps.length} argument${ps.length > 1 ? 's' : ''}.`); break; }
        body.args.forEach((a, i) => { if (a === v) acc.add(ps[i]); });
        break;
      }
      case 'not': usage(body.a, v, acc); break;
      case 'bin': usage(body.a, v, acc); usage(body.b, v, acc); break;
    }
    return acc;
  }
  function walk(x) {
    if (x.t === 'q') {
      let s = null;
      if (x.dom) s = sig.domAlias?.[x.dom] ?? null;
      const used = usage(x.body, x.v, new Set());
      if (used.size > 1) errors.push(`The variable ${x.v} is used for two different kinds of thing (${[...used].map((u) => sig.sortName?.[u] ?? u).join(' and ')}).`);
      if (!s) s = [...used][0] ?? sig.sorts[0];
      else if (used.size === 1 && !used.has(s)) errors.push(`${x.v} ranges over ${x.dom} but is used as a ${sig.sortName?.[[...used][0]] ?? [...used][0]}.`);
      sortOf.set(x, s);
      walk(x.body);
    } else if (x.t === 'not') walk(x.a);
    else if (x.t === 'bin') { walk(x.a); walk(x.b); }
    else if (x.t === 'atom') usage(x, '\u0000', new Set());
  }
  walk(n);
  // numbers name nothing in these settings (dogs, cats, people…)
  const things = Object.values(sig.sortPlural || {}).join(' and ') || Object.values(sig.sortName || {}).map((x) => x + 's').join(' and ') || 'objects';
  (function nums(x) {
    if (x.t === 'atom') { for (const a of x.args) if (/^\d/.test(a)) errors.push(`“${a}” doesn’t name anything here: the things are ${things}. Use variables bound by ∀ or ∃ instead of numbers.`); }
    else if (x.t === 'eq') { for (const a of [x.a, x.b]) if (/^\d/.test(a)) errors.push(`“${a}” doesn’t name anything here: the things are ${things}. Compare variables, like x = y.`); }
    else if (x.t === 'q') nums(x.body); else if (x.t === 'not') nums(x.a); else if (x.t === 'bin') { nums(x.a); nums(x.b); }
  })(n);
  return { sortOf, errors: [...new Set(errors)] };
}

function evalIn(n, world, env, sortOf) {
  switch (n.t) {
    case 'const': return n.v;
    case 'atom': {
      const tuple = n.args.map((a) => env[a]);
      if (tuple.some((t) => t === undefined)) throw new TypeErr('unbound');
      return world.rel[n.p].has(tuple.map((t) => t.i).join(','));
    }
    case 'eq': {
      const a = env[n.a], b = env[n.b];
      return a.s === b.s && a.i === b.i;
    }
    case 'not': return !evalIn(n.a, world, env, sortOf);
    case 'bin': {
      const a = evalIn(n.a, world, env, sortOf);
      if (n.op === 'and' && !a) return false;
      if (n.op === 'or' && a) return true;
      if (n.op === 'imp' && !a) return true;
      const b = evalIn(n.b, world, env, sortOf);
      switch (n.op) {
        case 'and': return a && b; case 'or': return a || b; case 'imp': return !a || b;
        case 'iff': return a === b; case 'xor': return a !== b;
      }
      return false;
    }
    case 'q': {
      const s = sortOf.get(n);
      const size = world.size[s];
      for (let i = 0; i < size; i++) {
        const r = evalIn(n.body, world, { ...env, [n.v]: { s, i } }, sortOf);
        if (n.q === 'all' && !r) return false;
        if (n.q === 'ex' && r) return true;
      }
      return n.q === 'all';
    }
  }
  throw new Error('bad node ' + n.t);
}

export function prepare(ast, sig) {
  const { ast: closed, free } = closure(ast);
  const { sortOf, errors } = typeCheck(closed, sig);
  return { closed, free, sortOf, errors };
}

export function evaluateIn(prepared, world) { return evalIn(prepared.closed, world, {}, prepared.sortOf); }

// Every world with each sort of size 1..maxSize (sampled when there are too many).
export function* worlds(sig, maxSize = 3, cap = 1 << 14) {
  const sorts = sig.sorts;
  const sizes = [];
  (function rec(i, cur) {
    if (i === sorts.length) { sizes.push({ ...cur }); return; }
    for (let n = 1; n <= maxSize; n++) rec(i + 1, { ...cur, [sorts[i]]: n });
  })(0, {});
  sizes.sort((a, b) => Object.values(a).reduce((x, y) => x + y) - Object.values(b).reduce((x, y) => x + y));
  for (const size of sizes) {
    const slots = [];
    for (const [p, ps] of Object.entries(sig.preds)) {
      const tuples = [];
      (function rec(i, cur) {
        if (i === ps.length) { tuples.push(cur.join(',')); return; }
        for (let e = 0; e < size[ps[i]]; e++) rec(i + 1, [...cur, e]);
      })(0, []);
      for (const t of tuples) slots.push([p, t]);
    }
    const total = 2 ** slots.length;
    const count = Math.min(total, cap);
    for (let m = 0; m < count; m++) {
      const mask = total > cap ? Math.floor(Math.random() * total) : m;
      const rel = Object.fromEntries(Object.keys(sig.preds).map((p) => [p, new Set()]));
      slots.forEach(([p, t], i) => { if (Math.floor(mask / 2 ** i) % 2 === 1) rel[p].add(t); });
      yield { size, rel };
    }
  }
}

// Compare two formulas on every small world. Returns {equiv, world, a, b} or {error}.
export function comparePred(userAst, refAst, sig, maxSize) {
  const u = prepare(userAst, sig);
  if (u.errors.length) return { error: u.errors[0] };
  const r = prepare(refAst, sig);
  if (r.errors.length) return { error: 'reference: ' + r.errors[0] };
  const ms = maxSize ?? (sig.sorts.length > 1 ? 3 : 3);
  try {
    for (const w of worlds(sig, ms)) {
      const a = evaluateIn(u, w), b = evaluateIn(r, w);
      if (a !== b) return { equiv: false, world: w, user: a, ref: b, free: u.free };
    }
  } catch {
    return { error: 'I couldn’t evaluate that formula. Use only the predicates given, applied to variables bound by ∀ or ∃.' };
  }
  return { equiv: true, free: u.free };
}

// Plain-English description of a small world for feedback.
export function describeWorld(w, scen) {
  const names = {};
  for (const s of Object.keys(w.size)) {
    names[s] = Array.from({ length: w.size[s] }, (_, i) => scen.sorts[s].label + (i + 1));
  }
  const parts = [];
  const sortList = Object.keys(w.size).map((s) => `${w.size[s]} ${w.size[s] === 1 ? scen.sorts[s].sing : scen.sorts[s].plural} (${names[s].join(', ')})`);
  parts.push('Imagine a world with ' + sortList.join(' and ') + '.');
  for (const [p, ps] of Object.entries(scen.preds)) {
    const rel = w.rel[p];
    if (ps.args.length === 1) {
      const yes = names[ps.args[0]].filter((_, i) => rel.has(String(i)));
      parts.push(yes.length ? `${listText(yes)} ${yes.length === 1 ? ps.is1 : ps.isN}.` : `Nothing ${ps.is1}.`);
    } else {
      const [s1, s2] = ps.args;
      const lines = names[s1].map((n1, i) => {
        const tgt = names[s2].filter((_, j) => rel.has(`${i},${j}`));
        return tgt.length ? `${n1} ${ps.verb} ${listText(tgt)}` : `${n1} ${ps.verbNone}`;
      });
      parts.push(lines.join('; ') + '.');
    }
  }
  return parts.join(' ');
}
function listText(xs) { return xs.length <= 1 ? xs.join('') : xs.slice(0, -1).join(', ') + ' and ' + xs[xs.length - 1]; }

// Generalised De Morgan / double negation moves, for the negation-pushing drill.
export function pushStep(n) { // all single moves anywhere
  const out = [];
  function rec(x, rebuild) {
    if (x.t === 'not' && x.a.t === 'q') out.push({ law: 'Generalised De Morgan', result: rebuild({ t: 'q', q: x.a.q === 'all' ? 'ex' : 'all', v: x.a.v, dom: x.a.dom, body: { t: 'not', a: x.a.body } }) });
    if (x.t === 'not' && x.a.t === 'not') out.push({ law: 'Double Negation', result: rebuild(x.a.a) });
    if (x.t === 'q') {
      // reverse De Morgan: ∀x ¬φ  ->  ¬∃x φ
      if (x.body.t === 'not') out.push({ law: 'Generalised De Morgan', result: rebuild({ t: 'not', a: { t: 'q', q: x.q === 'all' ? 'ex' : 'all', v: x.v, dom: x.dom, body: x.body.a } }) });
      rec(x.body, (b) => rebuild({ ...x, body: b }));
    } else if (x.t === 'not') rec(x.a, (a) => rebuild({ t: 'not', a }));
    else if (x.t === 'bin') { rec(x.a, (a) => rebuild({ ...x, a })); rec(x.b, (b) => rebuild({ ...x, b })); }
  }
  rec(n, (y) => y);
  return out;
}

export function checkPushStep(prev, next, maxApps = 3) {
  const target = keyPred(next);
  let frontier = [prev];
  const seen = new Set([keyPred(prev)]);
  for (let d = 1; d <= maxApps; d++) {
    const nf = [];
    for (const f of frontier) for (const m of pushStep(f)) {
      const k = keyPred(m.result);
      if (k === target) return { ok: true, apps: d };
      if (!seen.has(k)) { seen.add(k); nf.push(m.result); }
    }
    frontier = nf;
  }
  return { ok: false };
}

// Push all negations to the atoms (the simplified form).
export function pushAll(n) {
  switch (n.t) {
    case 'q': return { ...n, body: pushAll(n.body) };
    case 'bin': return { ...n, a: pushAll(n.a), b: pushAll(n.b) };
    case 'not': {
      const a = n.a;
      if (a.t === 'not') return pushAll(a.a);
      if (a.t === 'q') return { t: 'q', q: a.q === 'all' ? 'ex' : 'all', v: a.v, dom: a.dom, body: pushAll({ t: 'not', a: a.body }) };
      return { t: 'not', a: pushAll(a) };
    }
  }
  return n;
}
