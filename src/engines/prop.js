// Propositional logic engine: parsing, printing, evaluation and truth tables,
// following the COMPX361 conventions (binding priority ¬, ∧, ∨, ⊕, →, ↔; left binding;
// truth-table rows ordered by number of T's, as in the lecture notes).

export const SYM = { and: '∧', or: '∨', xor: '⊕', imp: '→', iff: '↔', nand: '↑', nor: '↓' };
export const OPS = Object.keys(SYM);
const PREC = { iff: 1, imp: 2, xor: 3, or: 4, and: 5, nand: 5, nor: 5 };

export const V = (name) => ({ t: 'var', name });
export const K = (v) => ({ t: 'const', v });
export const T_ = K(true);
export const F_ = K(false);
export const Not = (a) => ({ t: 'not', a });
export const Bin = (op, a, b) => ({ t: 'bin', op, a, b });
export const And = (a, b) => Bin('and', a, b);
export const Or = (a, b) => Bin('or', a, b);
export const Imp = (a, b) => Bin('imp', a, b);
export const Iff = (a, b) => Bin('iff', a, b);
export const Xor = (a, b) => Bin('xor', a, b);
export const Nand = (a, b) => Bin('nand', a, b);
export const Nor = (a, b) => Bin('nor', a, b);

export class ParseError extends Error {
  constructor(msg, pos) { super(msg); this.pos = pos; }
}

// ---------------------------------------------------------------- tokenizer
const KEYWORDS = [
  ['<->', 'iff'], ['<=>', 'BADIFF'], ['->', 'imp'], ['=>', 'BADIMP'],
  ['/\\', 'and'], ['\\/', 'or'], ['&&', 'and'], ['||', 'or'], ['(+)', 'xor'],
];
const WORDS = {
  and: 'and', or: 'or', not: 'not', xor: 'xor', nand: 'nand', nor: 'nor', iff: 'iff',
  implies: 'imp', true: 'T', false: 'F',
};
const CHARS = {
  '∧': 'and', '&': 'and', '^': 'and', '∨': 'or', '|': 'or', '⊕': 'xor', '→': 'imp', '↔': 'iff',
  '↑': 'nand', '↓': 'nor', '¬': 'not', '~': 'not', '!': 'not', '-': 'not', '⊤': 'T', '⊥': 'F',
  '(': 'lp', '[': 'lp', '{': 'lp', ')': 'rp', ']': 'rp', '}': 'rp', '⇔': 'BADIFF', '⇒': 'BADIMP',
  '⟹': 'BADIMP', '⟺': 'BADIFF', '≡': 'BADIFF', '∼': 'not', '⋀': 'and', '⋁': 'or',
};

export function tokenize(src) {
  const toks = [];
  let i = 0;
  const s = src;
  outer: while (i < s.length) {
    const c = s[i];
    if (/\s/.test(c)) { i++; continue; }
    for (const [kw, type] of KEYWORDS) {
      if (s.startsWith(kw, i)) { toks.push({ type, pos: i, text: kw }); i += kw.length; continue outer; }
    }
    if (/[a-z]/i.test(c)) {
      const m = /^[A-Za-z]+/.exec(s.slice(i))[0];
      const lw = m.toLowerCase();
      if (WORDS[lw] && m.length > 1) { toks.push({ type: WORDS[lw], pos: i, text: m }); i += m.length; continue; }
      if (c === 'T' || c === 'F') { toks.push({ type: c, pos: i, text: c }); i++; continue; }
      if (/[a-z]/.test(c)) {
        // single-letter variable, optional digit subscript or primes
        const vm = /^[a-z](?:_?\d+|'+)?/.exec(s.slice(i))[0];
        toks.push({ type: 'var', pos: i, text: vm.replace('_', '') });
        i += vm.length; continue;
      }
      throw new ParseError(`“${c}” isn't a propositional variable. Use lower-case letters (p, q, r…) for variables and T / F for true / false.`, i);
    }
    if (CHARS[c]) { toks.push({ type: CHARS[c], pos: i, text: c }); i++; continue; }
    throw new ParseError(`Unexpected character “${c}”.`, i);
  }
  toks.push({ type: 'eof', pos: s.length, text: '' });
  // ASCII “v” for ∨: a variable named v straight after an operand can only be “or”
  for (let j = 1; j < toks.length; j++) {
    if (toks[j].type === 'var' && toks[j].text === 'v' && ['var', 'T', 'F', 'rp'].includes(toks[j - 1].type)) toks[j] = { ...toks[j], type: 'or' };
  }
  return toks;
}

// ---------------------------------------------------------------- parser
const LEVELS = [['iff'], ['imp'], ['xor'], ['or'], ['and', 'nand', 'nor']];

export function parse(src) {
  if (typeof src !== 'string') throw new ParseError('No formula given.', 0);
  if (!src.trim()) throw new ParseError('Type a formula first.', 0);
  const toks = tokenize(src);
  let k = 0;
  const peek = () => toks[k];
  const next = () => toks[k++];

  function level(i) {
    if (i >= LEVELS.length) return unary();
    let left = level(i + 1);
    while (LEVELS[i].includes(peek().type)) {
      const op = next();
      const right = level(i + 1);
      left = Bin(op.type, left, right);
      left.pos = op.pos;
    }
    return left;
  }
  function unary() {
    const t = peek();
    if (t.type === 'not') { next(); const a = unary(); return Not(a); }
    if (t.type === 'lp') {
      next();
      if (peek().type === 'rp') throw new ParseError('Empty brackets.', peek().pos);
      const e = level(0);
      if (peek().type !== 'rp') throw new ParseError('Missing a closing bracket.', peek().pos);
      next();
      return { ...e, paren: true };
    }
    if (t.type === 'var') { next(); return V(t.text); }
    if (t.type === 'T') { next(); return K(true); }
    if (t.type === 'F') { next(); return K(false); }
    if (t.type === 'BADIFF') throw new ParseError('⇔ means “is logically equivalent to”; inside a formula use the connective ↔.', t.pos);
    if (t.type === 'BADIMP') throw new ParseError('⇒ means “logical consequence”; inside a formula use the connective →.', t.pos);
    if (t.type === 'eof') throw new ParseError('The formula ends too early: something is missing after the last connective.', t.pos);
    if (t.type === 'rp') throw new ParseError('Unexpected closing bracket.', t.pos);
    throw new ParseError(`Expected a variable, T, F, ¬ or “(” but found “${t.text}”.`, t.pos);
  }
  const e = level(0);
  const t = peek();
  if (t.type !== 'eof') {
    if (t.type === 'rp') throw new ParseError('Too many closing brackets.', t.pos);
    if (t.type === 'var' || t.type === 'lp' || t.type === 'T' || t.type === 'F' || t.type === 'not')
      throw new ParseError(`Missing a connective before “${t.text}”.`, t.pos);
    if (t.type === 'BADIFF') throw new ParseError('⇔ means “is logically equivalent to”; inside a formula use the connective ↔.', t.pos);
    if (t.type === 'BADIMP') throw new ParseError('⇒ means “logical consequence”; inside a formula use the connective →.', t.pos);
    throw new ParseError(`Unexpected “${t.text}”.`, t.pos);
  }
  checkNandBrackets(e);
  return e;
}

// ↑ and ↓ have no place in the course's binding-priority list, so insist on brackets
// whenever they are mixed with other binary connectives.
function checkNandBrackets(n) {
  if (n.t === 'not') return checkNandBrackets(n.a);
  if (n.t !== 'bin') return;
  const special = n.op === 'nand' || n.op === 'nor';
  for (const [side, c] of [['a', n.a], ['b', n.b]]) {
    if (c.t === 'bin' && !c.paren) {
      const cs = c.op === 'nand' || c.op === 'nor';
      if ((special || cs) && !(c.op === n.op && side === 'a')) {
        throw new ParseError(`Add brackets around the ${SYM[c.op]} part: ${SYM.nand} and ${SYM.nor} have no agreed binding priority.`, c.pos ?? 0);
      }
    }
    checkNandBrackets(c);
  }
}

export function tryParse(src) {
  try { return { ok: true, ast: parse(src) }; } catch (e) {
    return { ok: false, error: e.message, pos: e.pos ?? 0 };
  }
}

// ---------------------------------------------------------------- printing
// Lecturer style: every binary subformula of a binary formula is bracketed, except
// left-nested chains of ∧ or ∨ (p ∧ q ∧ r).
export function show(n) {
  switch (n.t) {
    case 'var': return n.name;
    case 'const': return n.v ? 'T' : 'F';
    case 'meta': return n.name;
    case 'not': return '¬' + (n.a.t === 'bin' ? '(' + show(n.a) + ')' : show(n.a));
    case 'bin': return wrap(n.a, n.op, 'L') + ' ' + SYM[n.op] + ' ' + wrap(n.b, n.op, 'R');
    default: return '?';
  }
}
function wrap(c, op, side) {
  if (c.t !== 'bin') return show(c);
  if (c.op === op && side === 'L' && (op === 'and' || op === 'or')) return show(c);
  return '(' + show(c) + ')';
}

// Minimal brackets according to the binding priority (used to set "insert the brackets" drills).
export function showMin(n) {
  switch (n.t) {
    case 'var': return n.name;
    case 'const': return n.v ? 'T' : 'F';
    case 'not': return '¬' + (n.a.t === 'bin' ? '(' + showMin(n.a) + ')' : showMin(n.a));
    case 'bin': {
      const p = PREC[n.op];
      const sp = (c) => c.t === 'bin' && (c.op === 'nand' || c.op === 'nor' || n.op === 'nand' || n.op === 'nor');
      const l = n.a.t === 'bin' && (PREC[n.a.op] < p || sp(n.a) && n.a.op !== n.op) ? '(' + showMin(n.a) + ')' : showMin(n.a);
      const r = n.b.t === 'bin' && (PREC[n.b.op] <= p || sp(n.b)) ? '(' + showMin(n.b) + ')' : showMin(n.b);
      return l + ' ' + SYM[n.op] + ' ' + r;
    }
  }
  return '?';
}

// Every binary subformula bracketed except the whole formula.
export function showFull(n, top = true) {
  switch (n.t) {
    case 'var': return n.name;
    case 'const': return n.v ? 'T' : 'F';
    case 'not': return '¬' + showFull(n.a, false);
    case 'bin': {
      const s = showFull(n.a, false) + ' ' + SYM[n.op] + ' ' + showFull(n.b, false);
      return top ? s : '(' + s + ')';
    }
  }
  return '?';
}

// Canonical key for hashing / equality (fully bracketed, no spaces).
export function key(n) {
  switch (n.t) {
    case 'var': return n.name;
    case 'const': return n.v ? 'T' : 'F';
    case 'meta': return '$' + n.name;
    case 'not': return '¬' + key(n.a);
    case 'bin': return '(' + key(n.a) + SYM[n.op] + key(n.b) + ')';
  }
  return '?';
}
export const same = (a, b) => key(a) === key(b);

export function isFullyBracketed(n, top = true) {
  if (n.t === 'not') return isFullyBracketed(n.a, false);
  if (n.t !== 'bin') return true;
  if (!top && !n.paren) return false;
  return isFullyBracketed(n.a, false) && isFullyBracketed(n.b, false);
}

// ---------------------------------------------------------------- semantics
export function evaluate(n, env) {
  switch (n.t) {
    case 'var': return !!env[n.name];
    case 'const': return n.v;
    case 'not': return !evaluate(n.a, env);
    case 'bin': {
      const a = evaluate(n.a, env), b = evaluate(n.b, env);
      switch (n.op) {
        case 'and': return a && b;
        case 'or': return a || b;
        case 'xor': return a !== b;
        case 'imp': return !a || b;
        case 'iff': return a === b;
        case 'nand': return !(a && b);
        case 'nor': return !(a || b);
      }
    }
  }
  throw new Error('bad node');
}

export function varsOf(n, acc = new Set()) {
  if (n.t === 'var') acc.add(n.name);
  else if (n.t === 'not') varsOf(n.a, acc);
  else if (n.t === 'bin') { varsOf(n.a, acc); varsOf(n.b, acc); }
  return acc;
}
export function sortVars(set) {
  return [...set].sort((x, y) => x.localeCompare(y));
}
export const vars = (...asts) => {
  const s = new Set();
  for (const a of asts) varsOf(a, s);
  return sortVars(s);
};

// Rows in the course order: by number of T's, then F before T from the left.
export function rows(vs) {
  const n = vs.length;
  const all = [];
  for (let m = 0; m < 1 << n; m++) {
    const bits = [];
    for (let i = 0; i < n; i++) bits.push(((m >> (n - 1 - i)) & 1) === 1);
    all.push(bits);
  }
  all.sort((x, y) => {
    const cx = x.filter(Boolean).length, cy = y.filter(Boolean).length;
    if (cx !== cy) return cx - cy;
    for (let i = 0; i < n; i++) if (x[i] !== y[i]) return x[i] ? 1 : -1;
    return 0;
  });
  return all.map((bits) => Object.fromEntries(vs.map((v, i) => [v, bits[i]])));
}

export function truthTable(n, vs = vars(n)) {
  return rows(vs).map((env) => ({ env, value: evaluate(n, env) }));
}

export function status(n, vs = vars(n)) {
  const tt = truthTable(n, vs);
  const models = tt.filter((r) => r.value).map((r) => r.env);
  const counter = tt.filter((r) => !r.value).map((r) => r.env);
  return {
    valid: counter.length === 0,
    satisfiable: models.length > 0,
    unsatisfiable: models.length === 0,
    models, counterexamples: counter, table: tt,
    label: counter.length === 0 ? 'valid' : models.length === 0 ? 'unsatisfiable' : 'satisfiable',
  };
}

export function equivalent(a, b) {
  const vs = vars(a, b);
  for (const env of rows(vs)) {
    if (evaluate(a, env) !== evaluate(b, env)) return { equiv: false, env, a: evaluate(a, env), b: evaluate(b, env) };
  }
  return { equiv: true };
}

export function consequence(p, q) { // does p ⇒ q ?
  const vs = vars(p, q);
  for (const env of rows(vs)) {
    if (evaluate(p, env) && !evaluate(q, env)) return { holds: false, env };
  }
  return { holds: true };
}

export function envText(env, vs = Object.keys(env)) {
  return vs.map((v) => `${v} = ${env[v] ? 'T' : 'F'}`).join(', ');
}

// Distinct non-atomic subformulas in build order (for truth-table columns).
export function subformulas(n) {
  const out = [];
  const seen = new Set();
  (function walk(x) {
    if (x.t === 'not') walk(x.a);
    if (x.t === 'bin') { walk(x.a); walk(x.b); }
    if (x.t === 'not' || x.t === 'bin') {
      const k = key(x);
      if (!seen.has(k)) { seen.add(k); out.push(x); }
    }
  })(n);
  return out;
}

export function connectives(n, acc = new Set()) {
  if (n.t === 'const') acc.add(n.v ? 'T' : 'F');
  if (n.t === 'not') { acc.add('not'); connectives(n.a, acc); }
  if (n.t === 'bin') { acc.add(n.op); connectives(n.a, acc); connectives(n.b, acc); }
  return acc;
}

export function size(n) {
  if (n.t === 'not') return 1 + size(n.a);
  if (n.t === 'bin') return 1 + size(n.a) + size(n.b);
  return 1;
}

export function strip(n) { // drop parse metadata
  if (n.t === 'var') return V(n.name);
  if (n.t === 'const') return K(n.v);
  if (n.t === 'meta') return { t: 'meta', name: n.name };
  if (n.t === 'not') return Not(strip(n.a));
  return Bin(n.op, strip(n.a), strip(n.b));
}

// Full disjunctive normal form read off a truth table (course row order).
export function fullDNF(fnRows, vs) {
  const terms = fnRows.filter((r) => r.value).map((r) => {
    let t = null;
    for (const v of vs) {
      const lit = r.env[v] ? V(v) : Not(V(v));
      t = t ? And(t, lit) : lit;
    }
    return t;
  });
  if (!terms.length) return And(V(vs[0]), Not(V(vs[0])));
  return terms.reduce((acc, t) => (acc ? Or(acc, t) : t), null);
}

// Position helpers: a path is an array of 'a' | 'b'.
export function at(n, path) {
  let x = n;
  for (const s of path) x = x[s];
  return x;
}
export function replaceAt(n, path, sub) {
  if (!path.length) return sub;
  const [h, ...rest] = path;
  if (n.t === 'not') return Not(replaceAt(n.a, rest, sub));
  return h === 'a' ? Bin(n.op, replaceAt(n.a, rest, sub), n.b) : Bin(n.op, n.a, replaceAt(n.b, rest, sub));
}
export function positions(n, path = [], acc = []) {
  acc.push(path);
  if (n.t === 'not') positions(n.a, [...path, 'a'], acc);
  if (n.t === 'bin') { positions(n.a, [...path, 'a'], acc); positions(n.b, [...path, 'b'], acc); }
  return acc;
}

// Tokens of the lecturer-style rendering with their subformula paths (for click-to-select UIs).
export function showTokens(n, path = []) {
  const out = [];
  function emit(text, p, kind) { out.push({ text, path: p, kind }); }
  function go(x, p) {
    switch (x.t) {
      case 'var': emit(x.name, p, 'var'); return;
      case 'const': emit(x.v ? 'T' : 'F', p, 'const'); return;
      case 'not':
        emit('¬', p, 'op');
        if (x.a.t === 'bin') { emit('(', [...p, 'a'], 'paren'); go(x.a, [...p, 'a']); emit(')', [...p, 'a'], 'paren'); } else go(x.a, [...p, 'a']);
        return;
      case 'bin': {
        const wrapL = x.a.t === 'bin' && !(x.a.op === x.op && (x.op === 'and' || x.op === 'or'));
        const wrapR = x.b.t === 'bin';
        if (wrapL) emit('(', [...p, 'a'], 'paren');
        go(x.a, [...p, 'a']);
        if (wrapL) emit(')', [...p, 'a'], 'paren');
        emit(' ' + SYM[x.op] + ' ', p, 'op');
        if (wrapR) emit('(', [...p, 'b'], 'paren');
        go(x.b, [...p, 'b']);
        if (wrapR) emit(')', [...p, 'b'], 'paren');
      }
    }
  }
  go(n, path);
  return out;
}
