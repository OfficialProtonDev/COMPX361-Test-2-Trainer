import { useState, useRef, useEffect, useMemo, useCallback } from 'preact/hooks';
import { tryParse, show as showProp } from '../engines/prop.js';
import { tryParsePred, showPred } from '../engines/pred.js';
import * as Alg from '../engines/algebra.js';
import { recordSolve, stats, subscribe } from './store.js';
import { newSeed } from '../engines/rng.js';

export { useState, useRef, useEffect, useMemo, useCallback };

export function cx(...a) { return a.filter(Boolean).join(' '); }

// ---------------------------------------------------------------- math text rendering
// Italicise single-letter variables like LaTeX, keep connectives upright.
// Long texts (sentences with maths in them) wrap; short formulas stay on one line.
export function MathText({ text, className = '', block = false, wrap, upright }) {
  const str = String(text ?? '');
  // grammar productions and derivations (anything with ⇒) are set upright, like the notes
  const parts = useMemo(() => tokenizeMath(str, upright ?? str.includes('⇒')), [str, upright]);
  const wraps = wrap ?? str.length > 44;
  return (
    <span class={cx('f', block && 'block', wraps && 'wrap', className)}>
      {parts.map((p, i) => (p.qf ? <span key={i} class="st">Q<sub>f</sub></span> : p.st ? <span key={i} class="st"><i>q</i><sub>{p.st}</sub></span>
        : p.v ? <i key={i}>{p.s}</i> : p.op ? <span key={i} class="op">{p.s}</span> : p.s))}
    </span>
  );
}
function tokenizeMath(s, upright = false) {
  const out = [];
  // state names q0, q1, … (also inside a production like aq1) get subscripts
  for (const [j, piece] of s.split(/(q\d+|Q_?f\b)/).entries()) {
    if (j % 2 === 1) { out.push(piece[0] === 'Q' ? { qf: true } : { st: piece.slice(1) }); continue; }
    const re = /([A-Za-z]+)|([¬∧∨→↔⊕↑↓⇒⇔∀∃∈≠≥≤])|([^A-Za-z¬∧∨→↔⊕↑↓⇒⇔∀∃∈≠≥≤]+)/g;
    let m;
    while ((m = re.exec(piece))) {
      if (m[1]) {
        const w = m[1];
        const after = piece.slice(re.lastIndex);
        // the article “a” (a state diagram) and list numerals (i.) are words, not variables
        const before = piece.slice(0, re.lastIndex - w.length);
        const word = (w === 'a' && /^ [A-Za-z]{2,}/.test(after) && !/^ (b|c|and|or)\b/.test(after)) || (w === 'i' && /^\./.test(after)) || (w === 's' && /\d$/.test(before) && !/^[A-Za-z0-9]/.test(after))
          || (/(^|\s)\($/.test(before) && /^\)/.test(after) && /^[a-h]$/.test(w) && s.length > 30);
        if (w.length === 1 && /[a-z]/.test(w) && !word && !upright) out.push({ s: w, v: true });
        else out.push({ s: w });
      } else if (m[2]) out.push({ s: m[2], op: true });
      else out.push({ s: m[3] });
    }
  }
  return out;
}
export const F = ({ children, block }) => <MathText text={children} block={block} />;

// ---------------------------------------------------------------- buttons & bits
export function Btn({ kind = '', sm, children, ...rest }) {
  return <button type="button" class={cx('btn', kind, sm && 'sm')} {...rest}>{children}</button>;
}
export function Seg({ value, options, onChange, label }) {
  return (
    <div class="seg" role="group" aria-label={label}>
      {options.map((o) => (
        <button type="button" key={o.value} class={cx(o.value === value && 'on')} aria-pressed={o.value === value} onClick={() => onChange(o.value)}>{o.label}</button>
      ))}
    </div>
  );
}
export const Chip = ({ kind = '', children, title }) => <span class={cx('chip', kind)} title={title}>{children}</span>;
export function Fb({ kind = 'info', children }) {
  const mark = { good: '✓', bad: '✗', hint: '!', info: 'i' }[kind];
  if (!children) return null;
  return <div class={cx('fb', kind)} role={kind === 'bad' ? 'alert' : 'status'}><span class="mark">{mark}</span><div>{children}</div></div>;
}

// ---------------------------------------------------------------- symbol bars + math fields
export const SYMS = {
  prop: ['¬', '∧', '∨', '→', '↔', '⊕', '↑', '↓', 'T', 'F', '(', ')'],
  nand: ['↑', '(', ')', '¬', '∧', '∨'],
  pred: ['∀', '∃', '¬', '∧', '∨', '→', '↔', ':', '≠', '=', '(', ')', ','],
  gram: ['⇒', '|', 'λ'],
  alg: ['^', '×', '(', ')', '≥', '>', '≤', '<', '=', '√'],
};

export function insertAt(el, text, value, setValue) {
  if (!el) { setValue((value || '') + text); return; }
  const s = el.selectionStart ?? value.length, e = el.selectionEnd ?? value.length;
  const nv = value.slice(0, s) + text + value.slice(e);
  setValue(nv);
  requestAnimationFrame(() => { try { el.focus(); el.setSelectionRange(s + text.length, s + text.length); } catch { /* ignore */ } });
}

export function SymBar({ set, targetRef, value, setValue, extra = [] }) {
  const list = [...(SYMS[set] || []), ...extra];
  return (
    <div class="symbar" aria-label="Insert a symbol">
      {list.map((s) => (
        <button type="button" key={s} class={cx('sym', s.length > 2 && 'wide')} tabIndex={-1}
          onMouseDown={(e) => e.preventDefault()}
          onClick={() => insertAt(targetRef.current, s === 'λ' ? 'λ' : s, value, setValue)}>{s}</button>
      ))}
    </div>
  );
}

// A text input for formulas with a live "reads as" preview.
export function MathField({ id, value, setValue, kind = 'prop', placeholder, onEnter, state, syms, label, extraSyms, rows = 1, hidePreview }) {
  const ref = useRef(null);
  const pv = useMemo(() => preview(kind, value), [kind, value]);
  const Tag = rows > 1 ? 'textarea' : 'input';
  return (
    <div class="field">
      {label && <label class="label" for={id}>{label}</label>}
      <Tag id={id} ref={ref} class={cx('input', kind === 'gram' || kind === 'code' ? 'code' : 'math', state === 'ok' && 'ok', state === 'bad' && 'bad')}
        value={value} placeholder={placeholder} spellcheck={false} autocomplete="off" autocapitalize="off" rows={rows}
        onInput={(e) => setValue(e.currentTarget.value)}
        onKeyDown={(e) => { if (e.key === 'Enter' && rows === 1 && onEnter) { e.preventDefault(); onEnter(); } }} />
      {syms !== false && <SymBar set={syms || kind} targetRef={ref} value={value} setValue={setValue} extra={extraSyms} />}
      {!hidePreview && value && value.trim() && (pv.error ? <div class="err">{pv.error}</div> : pv.text ? <div class="preview"><span class="lead">READS AS</span><MathText text={pv.text} /></div> : null)}
    </div>
  );
}

function preview(kind, value) {
  if (!value || !value.trim()) return {};
  if (kind === 'prop' || kind === 'nand') {
    const r = tryParse(value);
    return r.ok ? { text: showProp(r.ast) } : { error: r.error };
  }
  if (kind === 'pred') {
    const r = tryParsePred(value);
    return r.ok ? { text: showPred(r.ast) } : { error: r.error };
  }
  if (kind === 'alg') {
    try {
      if (/[=≥≤<>]/.test(value)) { const r = Alg.parseRelation(value); return { text: `${Alg.pretty(r.lhs)} ${r.rel} ${Alg.pretty(r.rhs)}` }; }
      return { text: Alg.pretty(Alg.parseExpr(value)) };
    } catch (e) { return { error: e.message }; }
  }
  return {};
}

// ---------------------------------------------------------------- steps
export function Step({ n, title, state = 'active', children, aside }) {
  return (
    <section class={cx('step', state)} aria-label={typeof title === 'string' ? `Step ${n}: ${title}` : `Step ${n}`}>
      <div class="step-head">
        <span class="step-num">{state === 'done' ? '✓' : state === 'revealed' ? '!' : n}</span>
        <span class="step-title">{title}</span>
        <span class="spacer" />
        {aside}
      </div>
      {state !== 'locked' && children}
    </section>
  );
}

// Multiple-choice options
export function Options({ options, picked, onPick, correct, reveal, keyLabels = 'ABCDEFG' }) {
  return (
    <div class="stack-sm">
      {options.map((o, i) => {
        const isPicked = picked === i;
        const cls = reveal ? (i === correct ? 'right' : isPicked ? 'wrong' : '') : isPicked ? 'picked' : '';
        return (
          <button type="button" key={i} class={cx('opt', cls)} onClick={() => !reveal && onPick(i)} aria-pressed={isPicked}>
            <span class="key">{keyLabels[i]}</span>
            <span>{typeof o === 'string' ? <MathOrText text={o} /> : o}</span>
          </button>
        );
      })}
    </div>
  );
}
export const MathOrText = ({ text }) => (/[∀∃¬∧∨→↔⊕↑↓{}≥≤ⁿ²ᵐ]/.test(text) ? <MathText text={text} /> : <span>{text}</span>);

// ---------------------------------------------------------------- drill frame
export function useProgress(id) {
  const [, force] = useState(0);
  useEffect(() => subscribe(() => force((x) => x + 1)), []);
  return stats(id);
}

export function Mastery({ id }) {
  const s = useProgress(id);
  const n = Math.min(3, s.clean || 0);
  return <span class="dots" title={`${s.clean || 0} clean solves, ${s.solved || 0} solved`}>{[0, 1, 2].map((i) => <span key={i} class={cx('dot', i < n && 'on')} />)}</span>;
}

export function DrillHeader({ kicker, title, sub, id, children }) {
  const s = useProgress(id);
  return (
    <header class="stack-sm">
      <div class="h-kicker">{kicker}</div>
      <h1 class="h-title">{title}</h1>
      {sub && <p class="h-sub">{sub}</p>}
      <div class="row" style={{ marginTop: '6px' }}>
        {children}
        <span class="spacer" />
        {id && <span class="small faint">{s.clean ? `${s.clean} clean ${s.clean === 1 ? 'solve' : 'solves'}` : s.solved ? `${s.solved} solved` : 'Not tried yet'}</span>}
        {id && <Mastery id={id} />}
      </div>
    </header>
  );
}

// Tracks whether the current question was solved without reveals, and records it once.
export function useSolve(id, seed) {
  const [revealed, setRevealed] = useState(false);
  const [solved, setSolved] = useState(false);
  useEffect(() => { setRevealed(false); setSolved(false); }, [seed]);
  const reveal = useCallback(() => setRevealed(true), []);
  // finish(false) records a solve that doesn't count as clean (e.g. some answers were wrong)
  const finish = useCallback((clean) => {
    setSolved((was) => { if (!was) recordSolve(id, !revealed && clean !== false); return true; });
  }, [id, revealed]);
  return { revealed, reveal, solved, finish };
}

export function useSeed(initial) {
  const [seed, setSeed] = useState(initial ?? newSeed());
  return [seed, () => setSeed(newSeed()), setSeed];
}

export function Toast({ text, onDone }) {
  useEffect(() => { if (!text) return; const t = setTimeout(onDone, 2200); return () => clearTimeout(t); }, [text]);
  return text ? <div class="toast" role="status">{text}</div> : null;
}

export function Collapse({ title, children, open = false }) {
  return (
    <details class="sol" open={open}>
      <summary>{title}</summary>
      <div>{children}</div>
    </details>
  );
}

export function ModelAnswer({ title = 'Model answer (lecturer’s layout)', lines, children }) {
  return (
    <div class="model">
      <div class="h-kicker">{title}</div>
      {lines && lines.map((l, i) => <div key={i} class={cx('model-line', /^\s{2,}/.test(l) && 'indent')}><MathText text={l.trim()} /></div>)}
      {children}
    </div>
  );
}

export function SolvedBanner({ clean, onNext, children, missed }) {
  return (
    <Fb kind={missed ? 'hint' : 'good'}>
      <div class="row">
        <strong>{missed ? 'Not this time.' : clean ? 'Solved cleanly.' : 'Solved.'}</strong>
        <span class="muted">{children}</span>
        <span class="spacer" />
        {onNext && <Btn kind="primary" sm onClick={onNext}>Next question</Btn>}
      </div>
    </Fb>
  );
}

export const TF = (b) => (b ? 'T' : 'F');
