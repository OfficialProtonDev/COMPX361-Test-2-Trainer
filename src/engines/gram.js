// Grammars (COMPX361 section 3): parsing, the course's grammar types, derivation checking,
// parse trees, language enumeration and "design a grammar" checking.

export const LAMBDA = 'λ';

// ---------------------------------------------------------------- symbols
export function tokenizeForm(text, knownVars = null) {
  const s = (text || '').replace(/\s+/g, '').replace(/[₀-₉]/g, (d) => String(d.charCodeAt(0) - 0x2080)).replace(/-/g, '−');
  if (s === '' || /^(λ|ε|lambda|eps|epsilon)$/i.test(s)) return [];
  const out = [];
  let i = 0;
  const known = knownVars ? [...knownVars].sort((a, b) => b.length - a.length) : null;
  while (i < s.length) {
    if (s[i] === 'λ' || s[i] === 'ε') { i++; continue; }
    if (known) {
      const m = known.find((v) => s.startsWith(v, i));
      if (m) { out.push(m); i += m.length; continue; }
    }
    const rest = s.slice(i);
    let m = /^Q_?f\b/.exec(rest) || /^Q_?f/.exec(rest);
    if (m && (!known || known.includes('Qf'))) { out.push('Qf'); i += m[0].length; continue; }
    m = /^q_?\d+/.exec(rest);
    if (m) { out.push(m[0].replace('_', '')); i += m[0].length; continue; }
    m = /^[A-Z](?:_\d+|'+)?/.exec(rest);
    if (m) { out.push(m[0].replace('_', '')); i += m[0].length; continue; }
    out.push(s[i]); i++;
  }
  return out;
}

export const isVarToken = (t) => /^[A-Z]/.test(t) || /^q\d+$/.test(t);
export const formText = (f) => (f.length ? f.join('') : LAMBDA);

// ---------------------------------------------------------------- grammar parsing
// Accepts "S ⇒ 0A | 1B | λ" lines, or "P = {S ⇒ 0A|λ, A ⇒ 1}".
export function parseGrammar(text, opts = {}) {
  let src = (text || '').trim();
  src = src.replace(/^P\s*=\s*/, '').replace(/^\{/, '').replace(/\}\s*\.?$/, '');
  const pieces = src.split(/[\n,;]+/).map((x) => x.trim()).filter(Boolean);
  const P = [];
  const errors = [];
  const arrowRe = /⇒|=>|->|→|::=|⟶/;
  for (const piece of pieces) {
    if (!arrowRe.test(piece)) { errors.push(`“${piece}” has no ⇒ arrow.`); continue; }
    const [l, r] = piece.split(arrowRe);
    const lhs = tokenizeForm(l, opts.V);
    if (!lhs.length) { errors.push(`The left side of “${piece}” is empty.`); continue; }
    if (!lhs.some(isVarToken) && !(opts.V && lhs.some((t) => opts.V.includes(t)))) {
      errors.push(`The left side of “${piece}” must contain a variable.`); continue;
    }
    const alts = r.split('|');
    if (alts.length > 1 && alts.some((a) => !a.trim())) { errors.push(`“${piece}” has an empty alternative next to “|”. Write λ if you mean the empty string.`); continue; }
    for (const alt of alts) {
      const rhs = tokenizeForm(alt, opts.V);
      if (!P.some((p) => p.lhs.join('\u0001') === lhs.join('\u0001') && p.rhs.join('\u0001') === rhs.join('\u0001'))) P.push({ lhs, rhs });
    }
  }
  if (!P.length && !errors.length) errors.push('Type at least one production, like S ⇒ 0S1 | λ.');
  const isVar = opts.V ? (t) => opts.V.includes(t) : isVarToken;
  const Vset = new Set(), Tset = new Set();
  for (const p of P) for (const t of [...p.lhs, ...p.rhs]) (isVar(t) ? Vset : Tset).add(t);
  const V = opts.V ? [...opts.V] : orderVars([...Vset], P);
  const S = opts.S ?? (Vset.has('S') ? 'S' : Vset.has('q0') ? 'q0' : P[0]?.lhs[0]);
  return { ok: errors.length === 0, errors, g: { V, T: [...Tset].sort(), S, P } };
}

function orderVars(vs, P) {
  const order = [];
  for (const p of P) for (const t of [...p.lhs, ...p.rhs]) if (vs.includes(t) && !order.includes(t)) order.push(t);
  return order;
}

export function grammarFromSpec(spec) { // spec: {V, T, S, P: {A: ['0A','1']}} or productions text
  if (typeof spec.P === 'string') return parseGrammar(spec.P, { V: spec.V, S: spec.S }).g;
  const P = [];
  for (const [l, alts] of Object.entries(spec.P)) for (const a of alts) P.push({ lhs: tokenizeForm(l, spec.V), rhs: tokenizeForm(a, spec.V) });
  return { V: spec.V, T: spec.T, S: spec.S, P };
}

// Lecturer-style text: P = {S ⇒ 0A|1B|λ, A ⇒ …}
export function showProductions(g, sep = ', ') {
  const groups = [];
  for (const p of g.P) {
    const l = p.lhs.join('');
    let grp = groups.find((x) => x.l === l);
    if (!grp) groups.push((grp = { l, r: [] }));
    grp.r.push(formText(p.rhs));
  }
  return groups.map((x) => `${x.l} ⇒ ${x.r.join(' | ')}`).join(sep);
}
export function showGrammar(g) {
  return `G = (V, T, S, P), where V = {${g.V.join(', ')}}, T = {${g.T.join(', ')}}, S = ${g.S} and P = {${showProductions(g)}}.`;
}

// ---------------------------------------------------------------- grammar types (course definitions)
export function classify(g) {
  const isVar = (t) => g.V.includes(t);
  const why = { regular: [], cf: [], cs: [] };
  for (const p of g.P) {
    const txt = `${p.lhs.join('')} ⇒ ${formText(p.rhs)}`;
    const single = p.lhs.length === 1 && isVar(p.lhs[0]);
    // regular: A ⇒ aB, A ⇒ a, S ⇒ λ
    const regOk = single && ((p.rhs.length === 2 && !isVar(p.rhs[0]) && isVar(p.rhs[1])) || (p.rhs.length === 1 && !isVar(p.rhs[0])) || (p.rhs.length === 0 && p.lhs[0] === g.S));
    if (!regOk) why.regular.push(txt + regReason(p, g));
    const cfOk = single && (p.rhs.length > 0 || p.lhs[0] === g.S);
    if (!cfOk) why.cf.push(txt + (single ? ' (only the start symbol may go to λ)' : ' (the left side must be a single variable)'));
    const csOk = p.rhs.length === 0 ? single && p.lhs[0] === g.S : csForm(p, isVar);
    if (!csOk) why.cs.push(txt + (p.rhs.length === 0 ? ' (only S ⇒ λ may erase)' : ' (not of the form βAγ ⇒ βαγ)'));
  }
  const type = !why.regular.length ? 'regular' : !why.cf.length ? 'context-free' : !why.cs.length ? 'context-sensitive' : 'unrestricted';
  return { type, why };
}
function regReason(p, g) {
  const isVar = (t) => g.V.includes(t);
  if (p.lhs.length !== 1 || !isVar(p.lhs[0])) return ' (left side must be one variable)';
  if (p.rhs.length === 0) return ' (only S ⇒ λ is allowed)';
  const nv = p.rhs.filter(isVar).length;
  if (nv > 1) return ' (more than one variable on the right)';
  if (nv === 1 && !isVar(p.rhs[p.rhs.length - 1])) return ' (the variable must come last)';
  if (p.rhs.length > 2 || (nv === 0 && p.rhs.length > 1)) return ' (only one terminal at a time)';
  if (nv === 1 && p.rhs.length === 1) return ' (a variable on its own is not allowed: A ⇒ aB or A ⇒ a)';
  return '';
}
function csForm(p, isVar) {
  for (let i = 0; i < p.lhs.length; i++) {
    if (!isVar(p.lhs[i])) continue;
    const beta = p.lhs.slice(0, i), gamma = p.lhs.slice(i + 1);
    if (p.rhs.length < beta.length + gamma.length + 1) continue;
    const startOk = beta.every((t, k) => p.rhs[k] === t);
    const endOk = gamma.every((t, k) => p.rhs[p.rhs.length - gamma.length + k] === t);
    if (startOk && endOk) return true;
  }
  return false;
}

export const TYPE_LABEL = { regular: 'Regular (type 3)', 'context-free': 'Context-free (type 2)', 'context-sensitive': 'Context-sensitive (type 1)', unrestricted: 'Arbitrary / unrestricted (type 0)' };

// ---------------------------------------------------------------- derivations
const eqArr = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);

export function applicable(form, g) {
  const out = [];
  g.P.forEach((p, pi) => {
    for (let i = 0; i + p.lhs.length <= form.length; i++) {
      if (p.lhs.every((t, k) => form[i + k] === t)) out.push({ pi, pos: i, result: [...form.slice(0, i), ...p.rhs, ...form.slice(i + p.lhs.length)] });
    }
  });
  return out;
}

export function verifyStep(prev, next, g) {
  const opts = applicable(prev, g).filter((o) => eqArr(o.result, next));
  if (opts.length) return { ok: true, options: opts };
  // diagnose
  let a = 0;
  while (a < prev.length && a < next.length && prev[a] === next[a]) a++;
  let b = 0;
  while (b < prev.length - a && b < next.length - a && prev[prev.length - 1 - b] === next[next.length - 1 - b]) b++;
  const from = prev.slice(a, prev.length - b), to = next.slice(a, next.length - b);
  const varsChanged = from.filter((t) => g.V.includes(t)).length;
  let msg;
  if (eqArr(prev, next)) msg = 'Nothing changed in this step.';
  else if (!from.length) msg = `You inserted “${formText(to)}” without replacing anything. Each step must replace the left side of a production.`;
  else if (!from.some((t) => g.V.includes(t))) msg = `You changed terminals (“${formText(from)}” → “${formText(to)}”). Terminals never change once they appear.`;
  else if (varsChanged > 1 && !g.P.some((p) => p.lhs.length > 1)) msg = `More than one variable changed (“${formText(from)}” → “${formText(to)}”). Apply exactly one production per ⇒.`;
  else msg = `“${formText(from)}” → “${formText(to)}” is not a production of G.`;
  return { ok: false, message: msg, from, to };
}

export function parseDerivation(text, g) {
  const parts = text.split(/⇒|=>|->|→/).map((x) => x.trim()).filter((x) => x.length);
  return parts.map((p) => tokenizeForm(p, g.V));
}

export function checkDerivation(forms, g, target) {
  const res = [];
  if (!forms.length) return { ok: false, steps: res, message: 'Write the derivation as S ⇒ … ⇒ the string.' };
  if (!eqArr(forms[0], [g.S])) return { ok: false, steps: res, message: `A derivation starts from the start symbol ${g.S}.` };
  for (let i = 1; i < forms.length; i++) {
    const r = verifyStep(forms[i - 1], forms[i], g);
    res.push(r);
    if (!r.ok) return { ok: false, steps: res, badStep: i, message: `Step ${i}: ${r.message}` };
  }
  const last = forms[forms.length - 1];
  if (last.some((t) => g.V.includes(t))) return { ok: false, steps: res, message: 'The last line still contains variables: keep going until only terminals are left.' };
  if (target != null && formText(last) !== target && !(target === '' && !last.length)) return { ok: false, steps: res, message: `This derives ${formText(last)}, not ${target}.` };
  return { ok: true, steps: res };
}

// Build a parse tree (context-free grammars only) from a list of (pi, pos) choices.
export function treeFromSteps(g, steps) {
  const root = { sym: g.S, kids: null };
  let leaves = [root];
  for (const s of steps) {
    const p = g.P[s.pi];
    const node = leaves[s.pos];
    node.kids = p.rhs.length ? p.rhs.map((sym) => ({ sym, kids: null })) : [{ sym: LAMBDA, kids: [], lambda: true }];
    leaves = [...leaves.slice(0, s.pos), ...(p.rhs.length ? node.kids : []), ...leaves.slice(s.pos + 1)];
  }
  return root;
}

export function treeFromForms(g, forms) {
  const steps = [];
  for (let i = 1; i < forms.length; i++) {
    const r = verifyStep(forms[i - 1], forms[i], g);
    if (!r.ok) return null;
    steps.push(r.options[0]);
  }
  return treeFromSteps(g, steps);
}

// ---------------------------------------------------------------- languages
export function isContextFree(g) {
  return g.P.every((p) => p.lhs.length === 1 && g.V.includes(p.lhs[0]));
}

export function language(g, maxLen) {
  return isContextFree(g) ? langCF(g, maxLen) : langBFS(g, maxLen);
}

function langCF(g, maxLen) {
  const L = Object.fromEntries(g.V.map((v) => [v, new Set()]));
  let changed = true, guard = 0;
  while (changed && guard++ < 100) {
    changed = false;
    for (const p of g.P) {
      const A = p.lhs[0];
      let cur = new Set(['']);
      for (const sym of p.rhs) {
        const nx = new Set();
        const opts = g.V.includes(sym) ? L[sym] : new Set([sym]);
        for (const s of cur) for (const t of opts) if (s.length + t.length <= maxLen) nx.add(s + t);
        cur = nx;
        if (!cur.size) break;
      }
      for (const s of cur) if (!L[A].has(s)) { L[A].add(s); changed = true; }
    }
  }
  return L[g.S] ?? new Set();
}

function langBFS(g, maxLen, cap = 150000) {
  const out = new Set();
  const start = [g.S];
  const seen = new Set([start.join('\u0001')]);
  let frontier = [start];
  const bound = maxLen + 3;
  while (frontier.length && seen.size < cap) {
    const nf = [];
    for (const f of frontier) {
      for (const o of applicable(f, g)) {
        const r = o.result;
        const terms = r.filter((t) => !g.V.includes(t)).length;
        if (terms > maxLen || r.length > bound) continue;
        const k = r.join('\u0001');
        if (seen.has(k)) continue;
        seen.add(k);
        if (r.every((t) => !g.V.includes(t))) out.add(r.join(''));
        else nf.push(r);
      }
    }
    frontier = nf;
  }
  return out;
}

// Find a derivation of w (BFS, leftmost for context-free grammars).
export function findDerivation(g, w, cap = 60000) {
  const target = [...w];
  const cf = isContextFree(g);
  const start = [g.S];
  const prev = new Map([[start.join('\u0001'), null]]);
  let frontier = [start];
  while (frontier.length && prev.size < cap) {
    const nf = [];
    for (const f of frontier) {
      let opts = applicable(f, g);
      if (cf) { const first = f.findIndex((t) => g.V.includes(t)); opts = opts.filter((o) => o.pos === first); }
      for (const o of opts) {
        const r = o.result;
        const k = r.join('\u0001');
        if (prev.has(k)) continue;
        const terms = r.filter((t) => !g.V.includes(t));
        if (terms.length > target.length || r.length > target.length + 4) continue;
        if (cf) { // terminal prefix must match
          let ok = true;
          for (let i = 0; i < r.length && !g.V.includes(r[i]); i++) if (r[i] !== target[i]) { ok = false; break; }
          if (!ok) continue;
        }
        prev.set(k, { from: f, step: o });
        if (eqArr(r, target)) {
          const forms = [r];
          let cur = k;
          while (prev.get(cur)) { const p = prev.get(cur); forms.unshift(p.from); cur = p.from.join('\u0001'); }
          return forms;
        }
        nf.push(r);
      }
    }
    frontier = nf;
  }
  return null;
}

// Compare a student's grammar with a target language on all strings up to maxLen.
export function checkDesign(g, target) {
  const { alphabet, test, maxLen = 8, requireType } = target;
  const bad = g.T.filter((t) => !alphabet.includes(t));
  if (bad.length) return { ok: false, message: `Your grammar uses symbols that aren't in the alphabet: ${bad.join(', ')}.` };
  if (!g.P.some((p) => p.lhs.length === 1 && p.lhs[0] === g.S)) return { ok: false, message: `There is no production for the start symbol ${g.S}.` };
  const cls = classify(g);
  let warning = null;
  if (requireType === 'regular' && cls.type !== 'regular') {
    return { ok: false, typeFail: true, message: `This grammar isn't regular by the course definition: ${cls.why.regular.slice(0, 2).join('; ')}. Regular productions look like A ⇒ aB, A ⇒ a or S ⇒ λ.` };
  }
  if (requireType === 'context-free') {
    const shape = g.P.filter((p) => !(p.lhs.length === 1 && g.V.includes(p.lhs[0])));
    if (shape.length) return { ok: false, typeFail: true, message: `This grammar isn't context-free: ${shape.map((p) => p.lhs.join('') + ' ⇒ ' + formText(p.rhs)).slice(0, 2).join('; ')} (the left side must be a single variable).` };
    const lam = g.P.filter((p) => !p.rhs.length && p.lhs[0] !== g.S);
    if (lam.length) warning = `Strictly, the course's definition of context-free only allows λ on the start symbol (S ⇒ λ), so ${lam.map((p) => p.lhs[0] + ' ⇒ λ').join(', ')} is not allowed. You can usually remove it by adding the λ-free alternatives directly (e.g. replace B ⇒ bB | λ by B ⇒ bB | b and add the cases without B).`;
  }
  const gen = language(g, maxLen);
  let missing = null, extra = null;
  for (const w of allStrings(alphabet, maxLen)) {
    const inT = test(w), inG = gen.has(w);
    if (inT && !inG && missing === null) missing = w;
    if (!inT && inG && extra === null) extra = w;
    if (missing !== null && extra !== null) break;
  }
  if (extra !== null) {
    const d = findDerivation(g, extra);
    return { ok: false, extra, derivation: d, message: `Your grammar generates ${extra || 'λ'}, which is not in the language.` };
  }
  if (missing !== null) return { ok: false, missing, message: `Your grammar cannot generate ${missing || 'λ'}, which is in the language.` };
  return { ok: true, type: cls.type, warning, message: `Correct: your grammar generates exactly the right strings (checked every string up to length ${maxLen}).` };
}

export function* allStrings(alphabet, maxLen) {
  yield '';
  let layer = [''];
  for (let n = 1; n <= maxLen; n++) {
    const nl = [];
    for (const s of layer) for (const a of alphabet) { nl.push(s + a); }
    for (const s of nl) yield s;
    layer = nl;
  }
}

// Course regular expressions (+ for union, λ for the empty string) → JS RegExp
export function regexToJS(re) {
  const body = re.replace(/\s+/g, '').replace(/λ/g, '').replace(/\+/g, '|');
  return new RegExp('^(?:' + body + ')$');
}
