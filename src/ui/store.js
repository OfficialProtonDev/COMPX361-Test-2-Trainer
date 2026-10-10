// Per-viewer progress, kept in this browser only (wrapped: storage may be unavailable).
const KEY = 'compx361-t2-trainer-v1';
let state = { drills: {}, mocks: [] };
try {
  const raw = window.localStorage.getItem(KEY);
  if (raw) state = { drills: {}, mocks: [], ...JSON.parse(raw) };
} catch { /* private mode etc. */ }

const subs = new Set();
function save() {
  try { window.localStorage.setItem(KEY, JSON.stringify(state)); } catch { /* ignore */ }
  for (const f of subs) f();
}

export function subscribe(f) { subs.add(f); return () => subs.delete(f); }
export function stats(id) { return state.drills[id] || { attempts: 0, solved: 0, clean: 0 }; }
export function recordSolve(id, clean) {
  const s = { ...stats(id) };
  s.attempts += 1; s.solved += 1; if (clean) s.clean += 1; s.last = Date.now();
  state.drills = { ...state.drills, [id]: s };
  save();
}
export function recordMock(entry) {
  state.mocks = [...state.mocks, { ...entry, at: Date.now() }].slice(-20);
  save();
}
export function upsertMock(entry) {
  const i = (state.mocks || []).findIndex((m) => m.id === entry.id);
  if (i < 0) { recordMock(entry); return; }
  const list = [...state.mocks];
  list[i] = { ...list[i], ...entry };
  state.mocks = list;
  save();
}
export function mocks() { return state.mocks || []; }
export function allStats() { return state.drills; }
export function getPref(k, d) { return state.prefs?.[k] ?? d; }
// Unsent written answers, so switching questions doesn't lose them.
export function getDraft(id) { return state.drafts?.[id] ?? ''; }
export function setDraft(id, text) {
  state.drafts = { ...(state.drafts || {}), [id]: text };
  try { window.localStorage.setItem(KEY, JSON.stringify(state)); } catch { /* ignore */ }
}
export function setPref(k, v) { state.prefs = { ...(state.prefs || {}), [k]: v }; save(); }
export function resetAll() { state = { drills: {}, mocks: [] }; save(); }
