import { render } from 'preact';
import { useState, useEffect, useErrorBoundary } from 'preact/hooks';
import { DRILLS, NAV, PAGES } from './registry.jsx';
import { Mastery, Btn, Seg, cx } from './kit.jsx';
import { getPref, setPref } from './store.js';
import { CODE } from '../engines/tmcode.js';

// Colour theme: 'system' follows the device (or the host page's data-theme, which we never touch);
// 'light' / 'dark' pin it through data-user-theme, which the CSS ranks above both.
const THEMES = ['light', 'system', 'dark'];
const THEME_LABEL = { light: 'Light', system: 'System', dark: 'Dark' };
function applyTheme(t) {
  try {
    if (t === 'light' || t === 'dark') document.documentElement.setAttribute('data-user-theme', t);
    else document.documentElement.removeAttribute('data-user-theme');
  } catch { /* ignore */ }
}
applyTheme(getPref('theme', 'system'));
function useTheme() {
  const [theme, setTheme] = useState(() => getPref('theme', 'system'));
  const set = (t) => { setTheme(t); setPref('theme', t); applyTheme(t); };
  return [theme, set];
}
function ThemeIcon({ t }) {
  const common = { class: 'ticon', viewBox: '0 0 16 16', 'aria-hidden': 'true', fill: 'none', stroke: 'currentColor', 'stroke-width': '1.5', 'stroke-linecap': 'round' };
  if (t === 'light') return <svg {...common}><circle cx="8" cy="8" r="3" /><path d="M8 1.6v1.5M8 12.9v1.5M1.6 8h1.5M12.9 8h1.5M3.5 3.5l1 1M11.5 11.5l1 1M3.5 12.5l1-1M11.5 4.5l1-1" /></svg>;
  if (t === 'dark') return <svg {...common}><path d="M13.4 9.7A5.6 5.6 0 0 1 6.3 2.6a5.6 5.6 0 1 0 7.1 7.1z" /></svg>;
  return <svg {...common}><circle cx="8" cy="8" r="5.6" /><path d="M8 2.4a5.6 5.6 0 0 1 0 11.2z" fill="currentColor" stroke="none" /></svg>;
}
function ThemeSeg({ theme, setTheme }) {
  return <Seg value={theme} onChange={setTheme} label="Colour theme" options={THEMES.map((t) => ({ value: t, label: <><ThemeIcon t={t} /><span class="tlabel">{THEME_LABEL[t]}</span></> }))} />;
}

// Route = location.hash token (#home, #p-laws, #paper-2024 …). Presets travel in memory.
let pendingPreset = null;
export function openDrill(id, preset) {
  pendingPreset = preset ? { ...preset, seed: preset.seed ?? 4242 } : null;
  if (location.hash.slice(1) === id) window.dispatchEvent(new HashChangeEvent('hashchange'));
  else location.hash = id;
  window.scrollTo({ top: 0 });
}
window.__openDrill = openDrill;

function useRoute() {
  const get = () => (location.hash || '#home').slice(1) || 'home';
  const [route, setRoute] = useState(get());
  const [preset, setPreset] = useState(null);
  const [nonce, setNonce] = useState(0);
  useEffect(() => {
    const f = () => { setRoute(get()); setPreset(pendingPreset); pendingPreset = null; setNonce((n) => n + 1); };
    window.addEventListener('hashchange', f);
    return () => window.removeEventListener('hashchange', f);
  }, []);
  return { route, preset, nonce };
}

export function Tape({ text = '14/10', size = 'sm' }) {
  // Paper tape punched with the course's 5-bit Turing code.
  const cells = [...text].map((ch) => CODE[ch] || '00000');
  return (
    <div class="tape" aria-hidden="true">
      {cells.map((code, i) => (
        <div key={i} class="tape-cell">
          {[...code].map((b, j) => (
            <span key={j} class={cx('tape-hole', b === '1' && 'on')} />
          ))}
        </div>
      ))}
    </div>
  );
}

function Rail({ route, open, onClose, theme, setTheme }) {
  return (
    <>
      {open && <div class="scrim" onClick={onClose} />}
      <nav class={cx('rail', open && 'open')} aria-label="Drills">
        <div class="brand">
          <Tape text="14/10" />
          <div class="brand-name">COMPX361 Test 2 Trainer<small>Wed 14 Oct · 6:15 pm · 40 marks</small></div>
          <div class="theme-seg"><ThemeSeg theme={theme} setTheme={setTheme} /></div>
        </div>
        {NAV.map((g) => (
          <div class="nav-group" key={g.title}>
            <div class="nav-title">{g.title}</div>
            {g.items.map((id) => {
              const d = DRILLS[id] || PAGES[id];
              if (!d) return null;
              return (
                <button type="button" key={id} class={cx('nav-item', route === id && 'on')} onClick={() => { location.hash = id; onClose(); window.scrollTo({ top: 0 }); }}>
                  <span class="nav-ico">{d.icon}</span>
                  <span>{d.title}</span>
                  {DRILLS[id] && <Mastery id={id} />}
                </button>
              );
            })}
          </div>
        ))}
        <p class="small faint" style={{ padding: '16px 8px 0' }}>Progress is saved in this browser only. Unofficial study aid, not from the course staff.</p>
      </nav>
    </>
  );
}

// If a page throws while rendering, show a way out instead of a frozen page.
function RouteBoundary({ route, children }) {
  const [error, resetError] = useErrorBoundary((e) => console.error(e));
  if (!error) return children;
  return (
    <div class="sheet">
      <section class="card stack">
        <div class="h-kicker">Something went wrong</div>
        <h1 class="h-title">This page hit an error</h1>
        <p class="muted">Your progress is safe. The error was: <code>{String(error?.message || error)}</code></p>
        <div class="row">
          <Btn kind="primary" onClick={resetError}>Try again</Btn>
          {route === 'mock' && <Btn onClick={() => { try { window.localStorage.removeItem('compx361-t2-mock-v1'); } catch { /* ignore */ } resetError(); }}>Discard the current mock test</Btn>}
          <Btn kind="ghost" onClick={() => { location.hash = 'home'; resetError(); }}>Back to the overview</Btn>
        </div>
      </section>
    </div>
  );
}

function App() {
  const { route, preset, nonce } = useRoute();
  const [open, setOpen] = useState(false);
  // Pages can open the phone drawer (the overview's "Browse all drills").
  useEffect(() => { const f = () => setOpen(true); window.addEventListener('t2:open-drills', f); return () => window.removeEventListener('t2:open-drills', f); }, []);
  const [theme, setTheme] = useTheme();
  const nextTheme = THEMES[(THEMES.indexOf(theme) + 1) % THEMES.length];
  const entry = DRILLS[route] || PAGES[route] || PAGES.home;
  const Comp = entry.C;
  useEffect(() => { document.title = route === 'home' ? 'COMPX361 Test 2 Trainer' : `${entry.title} · COMPX361 Test 2 Trainer`; }, [route]);
  return (
    <div class="shell">
      <Rail route={route} open={open} onClose={() => setOpen(false)} theme={theme} setTheme={setTheme} />
      <div class="main">
        <div class="topbar">
          <button type="button" class="btn sm" onClick={() => setOpen(true)} aria-label="Open the drill list">☰ Drills</button>
          <span class="brand-name" style={{ fontSize: '13px' }}>COMPX361 Test 2</span>
          <span class="spacer" />
          <button type="button" class="btn sm ghost theme-cycle" onClick={() => setTheme(nextTheme)} aria-label={`Colour theme: ${THEME_LABEL[theme]}. Switch to ${THEME_LABEL[nextTheme]}.`} title={`Theme: ${THEME_LABEL[theme]} (tap for ${THEME_LABEL[nextTheme]})`}>
            <ThemeIcon t={theme} /><span>{THEME_LABEL[theme]}</span>
          </button>
        </div>
        <RouteBoundary key={route + ':' + nonce} route={route}><Comp preset={preset} /></RouteBoundary>
      </div>
    </div>
  );
}

render(<App />, document.getElementById('app'));
