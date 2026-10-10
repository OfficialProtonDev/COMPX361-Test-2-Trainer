// Exact arithmetic expressions for checking induction algebra line by line.
// Numbers are exact rationals (BigInt) where possible, otherwise floats (for √2).

const gcd = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
export const Q = (n, d = 1n) => {
  n = BigInt(n); d = BigInt(d);
  if (d === 0n) throw new Error('Division by zero');
  if (d < 0n) { n = -n; d = -d; }
  const g = gcd(n, d) || 1n;
  return { n: n / g, d: d / g };
};
const F = (x) => ({ f: x });
const isF = (x) => x.f !== undefined;
const toF = (x) => (isF(x) ? x.f : Number(x.n) / Number(x.d));
export const num = toF;
export function add(a, b) { return isF(a) || isF(b) ? F(toF(a) + toF(b)) : Q(a.n * b.d + b.n * a.d, a.d * b.d); }
export function sub(a, b) { return isF(a) || isF(b) ? F(toF(a) - toF(b)) : Q(a.n * b.d - b.n * a.d, a.d * b.d); }
export function mul(a, b) { return isF(a) || isF(b) ? F(toF(a) * toF(b)) : Q(a.n * b.n, a.d * b.d); }
export function div(a, b) {
  if (isF(a) || isF(b)) { if (toF(b) === 0) throw new Error('Division by zero'); return F(toF(a) / toF(b)); }
  if (b.n === 0n) throw new Error('Division by zero');
  return Q(a.n * b.d, a.d * b.n);
}
export function pow(a, b) {
  if (!isF(b) && b.d === 1n && !isF(a)) {
    let e = b.n;
    if (e > 4000n || e < -4000n) return F(Math.pow(toF(a), toF(b)));
    if (e < 0n) { if (a.n === 0n) throw new Error('Division by zero'); return Q(a.d ** -e, a.n ** -e); }
    return Q(a.n ** e, a.d ** e);
  }
  return F(Math.pow(toF(a), toF(b)));
}
function sqrtQ(a) {
  if (!isF(a) && a.n >= 0n) {
    const r = (x) => { if (x < 2n) return x; let y = BigInt(Math.floor(Math.sqrt(Number(x)))); while (y * y > x) y--; while ((y + 1n) * (y + 1n) <= x) y++; return y; };
    const rn = r(a.n), rd = r(a.d);
    if (rn * rn === a.n && rd * rd === a.d) return Q(rn, rd);
  }
  return F(Math.sqrt(toF(a)));
}
export function cmp(a, b) {
  if (!isF(a) && !isF(b)) { const x = a.n * b.d - b.n * a.d; return x > 0n ? 1 : x < 0n ? -1 : 0; }
  const x = toF(a), y = toF(b);
  const tol = 1e-9 * Math.max(1, Math.abs(x), Math.abs(y));
  return Math.abs(x - y) <= tol ? 0 : x > y ? 1 : -1;
}
export const isInt = (a) => !isF(a) && a.d === 1n;
export const show = (a) => (isF(a) ? String(+a.f.toFixed(6)) : a.d === 1n ? String(a.n) : `${a.n}/${a.d}`);

// ---------------------------------------------------------------- parsing
export class ExprError extends Error { constructor(m, pos) { super(m); this.pos = pos; } }
const SUP = { '⁰': '0', '¹': '1', '²': '2', '³': '3', '⁴': '4', '⁵': '5', '⁶': '6', '⁷': '7', '⁸': '8', '⁹': '9' };

function lex(src) {
  const out = [];
  let i = 0;
  const s = src;
  while (i < s.length) {
    const c = s[i];
    if (/\s/.test(c)) { i++; continue; }
    if (SUP[c]) { // superscript digits become ^n
      let j = i; let d = '';
      while (j < s.length && SUP[s[j]]) { d += SUP[s[j]]; j++; }
      out.push({ t: 'op', v: '^', pos: i }, { t: 'num', v: d, pos: i });
      i = j; continue;
    }
    if (s.startsWith('...', i) || c === '…' || c === '⋯') { out.push({ t: 'dots', pos: i }); i += s.startsWith('...', i) ? 3 : 1; continue; }
    if (/[0-9]/.test(c) || (c === '.' && /[0-9]/.test(s[i + 1] || ''))) {
      const m = /^[0-9]*\.[0-9]+|^[0-9]+/.exec(s.slice(i))[0];
      out.push({ t: 'num', v: m, pos: i }); i += m.length; continue;
    }
    if (s.startsWith('sqrt', i)) { out.push({ t: 'id', v: 'sqrt', pos: i }); i += 4; continue; }
    if (c === '√') { out.push({ t: 'id', v: 'sqrt', pos: i }); i++; continue; }
    if (/[A-Za-z]/.test(c)) {
      out.push({ t: 'id', v: c, pos: i }); i++;
      if (s[i] === '_') { // subscript a_k, a_{k+1}, a_(k+1)
        i++;
        if (s[i] === '{' || s[i] === '(') {
          const close = s[i] === '{' ? '}' : ')';
          let depth = 0, j = i;
          for (; j < s.length; j++) { if (s[j] === s[i]) depth++; else if (s[j] === close && --depth === 0) break; }
          out.push({ t: 'sub', v: s.slice(i + 1, j), pos: i }); i = j + 1;
        } else {
          const m = /^[A-Za-z0-9]+/.exec(s.slice(i));
          if (!m) throw new ExprError('Something is missing after _.', i);
          out.push({ t: 'sub', v: m[0], pos: i }); i += m[0].length;
        }
      }
      continue;
    }
    const two = s.slice(i, i + 2);
    if (['>=', '<=', '!=', '=>', '=<'].includes(two)) { out.push({ t: 'rel', v: { '>=': '≥', '<=': '≤', '!=': '≠', '=>': '≥', '=<': '≤' }[two], pos: i }); i += 2; continue; }
    if ('=≥≤><≠'.includes(c)) { out.push({ t: 'rel', v: c, pos: i }); i++; continue; }
    if ('+-−–*×·/÷^()[]{},'.includes(c)) {
      const v = { '−': '-', '–': '-', '×': '*', '·': '*', '÷': '/', '[': '(', ']': ')', '{': '(', '}': ')' }[c] || c;
      out.push({ t: 'op', v, pos: i }); i++; continue;
    }
    throw new ExprError(`Unexpected “${c}”.`, i);
  }
  out.push({ t: 'eof', pos: s.length });
  return out;
}

const FUNCS = new Set(['S', 'a', 'sqrt', 'F', 'u', 'b']);

export function parseExpr(src, { funcs = FUNCS } = {}) {
  src = String(src ?? '').replace(/(?<!\.)\.\s*$/, '');
  if (!src.trim()) throw new ExprError('Type an expression first.', 0);
  const toks = lex(src);
  let k = 0;
  const peek = () => toks[k], next = () => toks[k++];
  const isOp = (v) => peek().t === 'op' && peek().v === v;

  function expr() {
    let left = term();
    while (isOp('+') || isOp('-')) {
      const op = next().v;
      if (peek().t === 'dots') throw new ExprError('dots', peek().pos);
      const right = term();
      left = { t: op === '+' ? 'add' : 'sub', a: left, b: right };
    }
    return left;
  }
  function term() {
    let left = unary();
    for (;;) {
      if (isOp('*') || isOp('/')) {
        const op = next().v;
        const right = unary();
        left = { t: op === '*' ? 'mul' : 'div', a: left, b: right };
      } else if (startsFactor()) {
        const right = power();
        left = { t: 'mul', a: left, b: right, implicit: true };
      } else break;
    }
    return left;
  }
  function startsFactor() {
    const t = peek();
    return t.t === 'num' || t.t === 'id' || (t.t === 'op' && t.v === '(');
  }
  function unary() {
    if (isOp('-')) { next(); return { t: 'neg', a: unary() }; }
    if (isOp('+')) { next(); return unary(); }
    return power();
  }
  function power() {
    const base = atom();
    if (isOp('^')) {
      next();
      const e = isOp('-') ? (next(), { t: 'neg', a: powerOperand() }) : powerOperand();
      return { t: 'pow', a: base, b: e };
    }
    return base;
  }
  function powerOperand() {
    // right associative: 2^k^2 = 2^(k^2)
    const b = atom();
    if (isOp('^')) { next(); return { t: 'pow', a: b, b: powerOperand() }; }
    return b;
  }
  function atom() {
    const t = peek();
    if (t.t === 'num') { next(); return { t: 'num', v: t.v.includes('.') ? decQ(t.v) : Q(t.v) }; }
    if (t.t === 'op' && t.v === '(') {
      next();
      const e = expr();
      if (!isOp(')')) throw new ExprError('Missing a closing bracket.', peek().pos);
      next();
      return { ...e, paren: true };
    }
    if (t.t === 'id') {
      next();
      if (peek().t === 'sub') { const s = next(); return { t: 'call', f: t.v, args: [parseExpr(s.v, { funcs })] }; }
      if (t.v === 'sqrt') {
        if (isOp('(')) { next(); const e = expr(); if (!isOp(')')) throw new ExprError('Missing “)”.', peek().pos); next(); return { t: 'call', f: 'sqrt', args: [e] }; }
        const a = atom(); return { t: 'call', f: 'sqrt', args: [a] };
      }
      if (funcs.has(t.v) && isOp('(')) {
        next();
        const e = expr();
        if (!isOp(')')) throw new ExprError('Missing “)”.', peek().pos);
        next();
        return { t: 'call', f: t.v, args: [e] };
      }
      return { t: 'var', name: t.v };
    }
    if (t.t === 'eof') throw new ExprError('The expression ends too early.', t.pos);
    if (t.t === 'rel') throw new ExprError(`Unexpected “${t.v}” here.`, t.pos);
    throw new ExprError(`Unexpected “${t.v ?? '…'}”.`, t.pos);
  }
  const e = expr();
  if (peek().t !== 'eof') {
    const t = peek();
    if (t.t === 'rel') throw new ExprError(`Write just an expression here (no “${t.v}”).`, t.pos);
    if (t.t === 'op' && t.v === ')') throw new ExprError('Too many closing brackets.', t.pos);
    throw new ExprError(`Unexpected “${t.v ?? '…'}”.`, t.pos);
  }
  return e;
}
function decQ(s) { const [i, f = ''] = s.split('.'); return Q(BigInt((i || '0') + f), 10n ** BigInt(f.length)); }

// "lhs REL rhs" (relation at top level).
export function parseRelation(src, opts) {
  const toks = lex(src);
  let depth = 0; let at = -1; let rel = null;
  for (const t of toks) {
    if (t.t === 'op' && t.v === '(') depth++;
    if (t.t === 'op' && t.v === ')') depth--;
    if (t.t === 'rel' && depth === 0) { if (at !== -1) throw new ExprError('Only one relation (=, ≥, >, ≤, <) please.', t.pos); at = t.pos; rel = t.v; }
  }
  if (at === -1) throw new ExprError('Write a relation like … = …  or  … ≥ … .', 0);
  const len = src.slice(at).startsWith('>=') || src.slice(at).startsWith('<=') || src.slice(at).startsWith('!=') ? 2 : 1;
  const L = src.slice(0, at), R = src.slice(at + len);
  return { lhs: parseSumOrExpr(L, opts), rel, rhs: parseSumOrExpr(R, opts), lhsText: L.trim(), rhsText: R.trim() };
}

// Accept written-out sums like 1·2 + 2·3 + ... + n(n+1); returns an expression node, or
// {t:'sumdots', terms:[…], last} when "..." is used.
export function parseSumOrExpr(src, opts) {
  if (!/\.\.\.|…|⋯/.test(src)) return parseExpr(src, opts);
  const parts = src.split(/\+\s*(?:\.\.\.|…|⋯)\s*\+/);
  if (parts.length !== 2) throw new ExprError('Write a sum as  first + second + ... + last.', 0);
  const head = parts[0].split(/\+(?![^(]*\))/).map((x) => x.trim()).filter(Boolean).map((x) => parseExpr(x, opts));
  const after = parts[1].split(/\+(?![^(]*\))/).map((x) => x.trim()).filter(Boolean).map((x) => parseExpr(x, opts));
  if (!after.length) throw new ExprError('Write a sum as  first + second + ... + last.', 0);
  return { t: 'sumdots', head, tail: after.slice(0, -1), last: after[after.length - 1] };
}

// ---------------------------------------------------------------- evaluation
export function evaluate(node, env = {}, fns = {}) {
  switch (node.t) {
    case 'num': return node.v;
    case 'var': {
      if (env[node.name] === undefined) throw new ExprError(`I don't know what “${node.name}” is here.`, 0);
      const v = env[node.name];
      return typeof v === 'function' ? v(env) : v;
    }
    case 'add': return add(evaluate(node.a, env, fns), evaluate(node.b, env, fns));
    case 'sub': return sub(evaluate(node.a, env, fns), evaluate(node.b, env, fns));
    case 'mul': return mul(evaluate(node.a, env, fns), evaluate(node.b, env, fns));
    case 'div': return div(evaluate(node.a, env, fns), evaluate(node.b, env, fns));
    case 'pow': return pow(evaluate(node.a, env, fns), evaluate(node.b, env, fns));
    case 'neg': return sub(Q(0), evaluate(node.a, env, fns));
    case 'call': {
      const args = node.args.map((a) => evaluate(a, env, fns));
      if (node.f === 'sqrt') return sqrtQ(args[0]);
      const f = fns[node.f];
      if (!f) throw new ExprError(`“${node.f}( )” isn't defined in this question.`, 0);
      return f(args[0]);
    }
    case 'sumdots': throw new ExprError('A “…” sum can only be used where the question’s sum is meant.', 0);
  }
  throw new Error('bad node ' + node.t);
}

// Free variables used.
export function varsIn(node, acc = new Set()) {
  if (node.t === 'var') acc.add(node.name);
  for (const c of [node.a, node.b, ...(node.args || []), ...(node.head || []), node.last]) if (c) varsIn(c, acc);
  return acc;
}
export function callsIn(node, acc = new Set()) {
  if (node.t === 'call') acc.add(node.f);
  for (const c of [node.a, node.b, ...(node.args || []), ...(node.head || []), node.last]) if (c) callsIn(c, acc);
  return acc;
}

// Pretty print (k², fractions as a/b, explicit ·)
const PREC = { add: 1, sub: 1, mul: 2, div: 2, neg: 3, pow: 4 };
const SUPS = '⁰¹²³⁴⁵⁶⁷⁸⁹';
export function pretty(n) {
  switch (n.t) {
    case 'num': return show(n.v);
    case 'var': return n.name;
    case 'call': {
      if (n.f === 'sqrt') return '√' + wrapP(n.args[0], 5);
      const inner = pretty(n.args[0]);
      if (n.f === 'a') return inner.length === 1 ? 'a_' + inner : 'a_{' + inner + '}';
      return `${n.f}(${inner})`;
    }
    case 'neg': return '−' + wrapP(n.a, 3);
    case 'pow': {
      const b = n.a.t === 'call' && n.a.f === 'sqrt' ? '(' + pretty(n.a) + ')' : wrapP(n.a, 5);
      if (n.b.t === 'num' && isInt(n.b.v) && n.b.v.n >= 0n && n.b.v.n < 10n) return b + SUPS[Number(n.b.v.n)];
      return b + '^' + (n.b.t === 'num' || n.b.t === 'var' ? pretty(n.b) : '(' + pretty(n.b) + ')');
    }
    case 'add': return keepP(n.a) + ' + ' + wrapP(n.b, 1, true);
    case 'sub': return keepP(n.a) + ' − ' + wrapP(n.b, 1, true);
    case 'mul': {
      const L = wrapP(n.a, 2), R = wrapP(n.b, 2, true);
      const endsDigit = /[0-9]$/.test(L), endsClose = /[)}]$/.test(L), endsLetter = /[a-z²³⁴⁵⁶⁷⁸⁹⁰¹]$/.test(L);
      const implicit = (endsDigit && /^[a-z(√]/.test(R)) || (endsClose && /^[a-z(√]/.test(R)) || (endsLetter && /^\(/.test(R));
      return implicit ? L + R : L + ' × ' + R;
    }
    case 'div': return wrapP(n.a, 2) + '/' + wrapP(n.b, 3, true);
    case 'sumdots': return n.head.map(pretty).join(' + ') + ' + ⋯ + ' + [...(n.tail || []), n.last].map(pretty).join(' + ');
  }
  return '?';
}
function keepP(c) { return c.paren && (c.t === 'add' || c.t === 'sub') ? '(' + pretty(c) + ')' : pretty(c); }
function wrapP(c, p, right = false) {
  if (c.paren && (c.t === 'add' || c.t === 'sub')) return '(' + pretty(c) + ')';
  const cp = c.t === 'num' && (c.v.n < 0n || c.v.d !== 1n) ? 2.5 : PREC[c.t] ?? 9;
  return cp < p || (right && cp === p && (c.t === 'sub' || c.t === 'add' || c.t === 'div' || c.t === 'mul')) ? '(' + pretty(c) + ')' : pretty(c);
}

// Compare a relation numerically over a range of k values.
export function holdsOver(aNode, rel, bNode, ks, envFor, fns) {
  for (const k of ks) {
    const env = envFor(k);
    let a, b;
    try { a = evaluate(aNode, env, fns); b = evaluate(bNode, env, fns); } catch (e) { return { ok: false, error: e.message, k }; }
    const c = cmp(a, b);
    const ok = rel === '=' ? c === 0 : rel === '≥' ? c >= 0 : rel === '>' ? c > 0 : rel === '≤' ? c <= 0 : rel === '<' ? c < 0 : c !== 0;
    if (!ok) return { ok: false, k, a, b };
  }
  return { ok: true };
}
