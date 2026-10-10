import { useState, useEffect, useRef } from 'preact/hooks';
import { Btn, Fb, cx, MathText } from './kit.jsx';
import { getDraft, setDraft } from './store.js';
import { CLAUDE_URL } from './host.js';

// The page asks Claude through the artifact's `sample` capability (each viewer's own account).
let samplePromise = null;
export function getSample() {
  if (!samplePromise) {
    samplePromise = (async () => {
      try {
        if (!window.claude || typeof window.claude.use !== 'function') return null;
        return await window.claude.use('sample');
      } catch { return null; }
    })();
  }
  return samplePromise;
}

export function useSampleAvailable() {
  const [ok, setOk] = useState(null);
  useEffect(() => { let live = true; getSample().then((s) => live && setOk(!!s)); return () => { live = false; }; }, []);
  return ok;
}

const CODES = {
  not_granted: 'Claude marking isn’t allowed for this page in your browser. Use the checklist instead.',
  sampling_disabled: 'Claude isn’t available on your account here. Use the checklist instead.',
  rate_limited: 'Claude is busy or you’ve hit a usage limit. Try again in a little while, or use the checklist.',
  session_expired: 'Sign in to Claude again to use marking.',
  invalid_json: 'The marking came back garbled. Press “Mark with Claude” again.',
  refused: 'Claude declined to mark this answer. Use the checklist instead.',
  not_declared: 'Claude marking isn’t switched on for this page. Use the checklist instead.',
  capability_disabled: 'Claude marking isn’t available in this view. Use the checklist instead.',
  capability_removed: 'This Claude app is too old for marking here. Use the checklist instead.',
  empty_completion: 'Claude returned an empty mark. Press “Mark with Claude” again, or use the checklist.',
  upstream_error: 'The connection to Claude dropped. Press “Mark with Claude” again in a moment.',
};

export async function askMark({ question, marks, model, scheme, answer, notes }, signal) {
  const sample = await getSample();
  if (!sample) throw { code: 'not_granted' };
  const prompt = `You are marking a student's answer to a question from COMPX361 Logic and Computation (University of Waikato), Test 2, in the way the course lecturer marks: credit for correct content and correct setting-out, strict about precise statements, but no penalty for harmless differences in wording or notation (ASCII like -> for →, or ^ for powers, is fine). The model answer is the lecturer's (or written in his layout); the mark split below is a guide.

QUESTION (${marks} marks):
${question}

MODEL ANSWER (the lecturer's where one exists, otherwise written in his layout):
${model}

MARK SCHEME:
${scheme.map((s) => `- [${s.m}] ${s.p}`).join('\n')}
${notes ? `\nNOTES FOR THE MARKER:\n${notes}\n` : ''}
STUDENT'S ANSWER (between the markers):
<<<
${answer}
>>>

Mark it. Award marks in multiples of 0.5, never more than each point's maximum. Reply with only a JSON object, no other text:
{"score": number, "max": ${marks}, "points": [{"point": "short name of the mark-scheme point", "awarded": number, "max": number, "comment": "one short sentence"}], "feedback": "two or three sentences of specific advice", "fix": "the single most important correction, or an empty string"}`;
  const r = await sample.json(prompt, { signal, modelTier: 'default' });
  if (!r || typeof r.score !== 'number' || !Array.isArray(r.points)) throw { code: 'invalid_json' };
  r.score = Math.max(0, Math.min(marks, Math.round(r.score * 2) / 2));
  return r;
}

// Written-answer box: Claude marking when available, a self-marking checklist otherwise.
export function WrittenAnswer({ id, question, marks, model, scheme, notes, placeholder, rows = 7, onScore, initial = '', splitNote = 'a suggested split (the official solutions give none)' }) {
  const avail = useSampleAvailable();
  const [text, setTextRaw] = useState(() => getDraft(id) || initial);
  const setText = (v) => { setTextRaw(v); setDraft(id, v); };
  const [busy, setBusy] = useState(false);
  const [res, setRes] = useState(null);
  const [err, setErr] = useState(null);
  const [selfMarks, setSelfMarks] = useState({});
  const [showModel, setShowModel] = useState(false);
  const ctl = useRef(null);
  useEffect(() => () => ctl.current?.abort(), []);
  const mark = async () => {
    if (!text.trim()) { setErr('Write your answer first.'); return; }
    setBusy(true); setErr(null); setRes(null);
    ctl.current = new AbortController();
    try {
      const r = await askMark({ question, marks, model, scheme, answer: text, notes }, ctl.current.signal);
      setRes(r); onScore && onScore(r.score, 'claude');
    } catch (e) {
      if (e?.code !== 'cancelled') setErr(CODES[e?.code] || 'Marking failed. Try again, or use the checklist.');
    } finally { setBusy(false); }
  };
  const selfTotal = scheme.reduce((s, p, i) => s + (selfMarks[i] ? p.m : 0), 0);
  return (
    <div class="stack">
      <textarea id={id} class="input" rows={rows} value={text} placeholder={placeholder} onInput={(e) => setText(e.currentTarget.value)} aria-label="Your answer" spellcheck={true} />
      <div class="step-actions">
        {avail && <Btn kind="primary" onClick={mark} disabled={busy}>{busy ? 'Marking…' : res ? 'Mark again' : 'Mark with Claude'}</Btn>}
        {busy && <Btn kind="ghost" onClick={() => ctl.current?.abort()}>Stop</Btn>}
        <Btn kind={avail ? 'ghost' : 'primary'} onClick={() => setShowModel((s) => !s)}>{showModel ? 'Hide model answer' : 'Show model answer & checklist'}</Btn>
        {avail === false && <span class="small faint">{CLAUDE_URL ? <>Claude marking works when you <a href={CLAUDE_URL} target="_blank" rel="noopener">open the trainer in Claude</a>; the checklist works everywhere.</> : 'Claude marking needs the page opened inside Claude; the checklist works everywhere.'}</span>}
      </div>
      {busy && <Fb kind="info">Claude is reading your answer against the model answer and the mark split. This can take up to a minute.</Fb>}
      {err && <Fb kind="hint">{err}</Fb>}
      {res && (
        <div class="card flat mark-result">
          <div class="row"><span class="score-big" style={{ fontSize: '30px' }}>{res.score} / {res.max ?? marks}</span><span class="spacer" /><span class="small faint">Marked by Claude against the model answer; mark split {splitNote}</span></div>
          {res.points.map((p, i) => (
            <div key={i} class="mark-point"><span class={cx('m', p.awarded >= p.max ? 'status ok' : p.awarded > 0 ? '' : 'status bad')}>{p.awarded >= p.max ? '✓' : p.awarded > 0 ? '½' : '✗'}</span>
              <div><strong>{p.point}</strong> <span class="muted">{p.comment}</span></div><span class="mono">{p.awarded}/{p.max}</span></div>
          ))}
          {res.feedback && <p class="muted">{res.feedback}</p>}
          {res.fix && <Fb kind="hint">{res.fix}</Fb>}
        </div>
      )}
      {showModel && (
        <div class="model">
          <div class="h-kicker">Model answer</div>
          {model.split('\n').map((l, i) => <div key={i} class="model-line"><MathText text={l} /></div>)}
          <div class="h-kicker" style={{ marginTop: '8px' }}>Self-mark: tick what your answer has</div>
          {scheme.map((s, i) => (
            <label key={i} class="row" style={{ gap: '8px', alignItems: 'flex-start' }}>
              <input type="checkbox" checked={!!selfMarks[i]} onChange={(e) => { const v = e.currentTarget.checked; setSelfMarks((m) => { const n = { ...m, [i]: v }; onScore && onScore(scheme.reduce((t, p, j) => t + (n[j] ? p.m : 0), 0), 'self'); return n; }); }} />
              <span>{s.p} <span class="mono faint">[{s.m}]</span></span>
            </label>
          ))}
          <div class="small"><strong>Self-marked: {selfTotal} / {marks}</strong></div>
        </div>
      )}
    </div>
  );
}
