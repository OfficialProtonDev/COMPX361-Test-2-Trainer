import { useMemo } from 'preact/hooks';

// ---------------------------------------------------------------- state names (q₀, Q_f, S …)
export function StateLabel({ name, x, y, size = 16 }) {
  const m = /^([A-Za-z]+?)_?(\d+|f)$/.exec(name);
  const italic = /^[A-Za-z]/.test(name);
  if (m && (m[1] === 'q' || m[1] === 'Q')) {
    return (
      <text x={x} y={y + size * 0.34} text-anchor="middle" font-size={size} style={{ fill: 'var(--ink)' }}>
        <tspan font-style="italic">{m[1]}</tspan>
        <tspan font-size={size * 0.68} dy={size * 0.28} font-style={m[2] === 'f' ? 'italic' : 'normal'}>{m[2]}</tspan>
      </text>
    );
  }
  return <text x={x} y={y + size * 0.34} text-anchor="middle" font-size={name.length > 3 ? size * 0.8 : size} font-style={italic && name.length <= 2 ? 'italic' : 'normal'} style={{ fill: 'var(--ink)' }}>{name}</text>;
}

// ---------------------------------------------------------------- automaton / TM diagrams
const R = 21;

export function autoLayout(states, start, edges, { last = [], gapX = 150, gapY = 104 } = {}) {
  const layer = { [start]: 0 };
  const order = [start];
  const q = [start];
  while (q.length) {
    const s = q.shift();
    for (const e of edges) {
      if (e.from === s && layer[e.to] === undefined && !last.includes(e.to)) { layer[e.to] = layer[s] + 1; order.push(e.to); q.push(e.to); }
    }
  }
  let maxL = Math.max(0, ...Object.values(layer));
  for (const s of states) if (layer[s] === undefined && !last.includes(s)) { layer[s] = ++maxL; order.push(s); }
  if (last.length) { maxL += 1; for (const s of last) { layer[s] = maxL; order.push(s); } }
  const byL = {};
  for (const s of order) (byL[layer[s]] ||= []).push(s);
  const maxCount = Math.max(...Object.values(byL).map((a) => a.length));
  const pos = {};
  for (const [L, list] of Object.entries(byL)) {
    list.forEach((s, i) => { pos[s] = { x: 70 + Number(L) * gapX, y: 80 + (i - (list.length - 1) / 2) * gapY + ((maxCount - 1) * gapY) / 2 }; });
  }
  return pos;
}

function unit(dx, dy) { const d = Math.hypot(dx, dy) || 1; return [dx / d, dy / d]; }

export function Automaton({ states, start, accept = [], edges, pos: givenPos, last, title, height, highlight = {}, numeric = false }) {
  // edges: [{from, to, labels:[], cls}]
  const pos = useMemo(() => givenPos || autoLayout(states, start, edges, { last }), [states, start, edges, givenPos, last]);
  const xs = states.map((s) => pos[s]?.x ?? 0), ys = states.map((s) => pos[s]?.y ?? 0);
  const cy = (Math.min(...ys) + Math.max(...ys)) / 2;
  const minX = Math.min(...xs) - 70, maxX = Math.max(...xs) + 60, minY = Math.min(...ys) - 78, maxY = Math.max(...ys) + 78;
  const W = maxX - minX, H = maxY - minY;
  const has = (a, b) => edges.some((e) => e.from === a && e.to === b);
  const items = edges.map((e, idx) => {
    const P = pos[e.from], Q = pos[e.to];
    if (!P || !Q) return null;
    const label = e.labels.join(', ');
    const color = e.cls === 'missing' || e.cls === 'extra' ? 'var(--marker)' : e.cls === 'ok' ? 'var(--tick)' : e.cls === 'hl' ? 'var(--biro)' : 'var(--ink)';
    const dash = e.cls === 'missing' ? '5 4' : undefined;
    if (e.from === e.to) {
      const down = P.y > cy + 1;
      const s = down ? 1 : -1;
      const a1 = [P.x - 12, P.y + s * (R - 4)], a2 = [P.x + 12, P.y + s * (R - 4)];
      const c1 = [P.x - 30, P.y + s * (R + 40)], c2 = [P.x + 30, P.y + s * (R + 40)];
      const d = `M ${a1[0]} ${a1[1]} C ${c1[0]} ${c1[1]} ${c2[0]} ${c2[1]} ${a2[0]} ${a2[1]}`;
      return { key: idx, d, color, dash, lx: P.x, ly: P.y + s * (R + 38) + (down ? 14 : -4), label, cls: e.cls };
    }
    let off = 0;
    const [ux, uy] = unit(Q.x - P.x, Q.y - P.y);
    const nx = uy, ny = -ux; // normal; a positive offset bends forward edges up and backward edges down
    if (has(e.to, e.from)) off = 26;
    else {
      // bend around any node sitting on the straight line
      for (const s of states) {
        if (s === e.from || s === e.to || !pos[s]) continue;
        const N = pos[s];
        const vx = Q.x - P.x, vy = Q.y - P.y;
        const t = ((N.x - P.x) * vx + (N.y - P.y) * vy) / (vx * vx + vy * vy);
        if (t <= 0 || t >= 1) continue;
        const dist = Math.hypot(N.x - (P.x + t * vx), N.y - (P.y + t * vy));
        if (dist < R + 16) {
          const mx0 = (P.x + Q.x) / 2, my0 = (P.y + Q.y) / 2;
          const dPlus = Math.hypot(mx0 + nx * 90 - N.x, my0 + ny * 90 - N.y), dMinus = Math.hypot(mx0 - nx * 90 - N.x, my0 - ny * 90 - N.y);
          off = dist < 2 ? 40 : dPlus >= dMinus ? 40 : -40;
          break;
        }
      }
    }
    const mx = (P.x + Q.x) / 2 + nx * off * 1.6, my = (P.y + Q.y) / 2 + ny * off * 1.6;
    const [sx, sy] = unit(mx - P.x, my - P.y);
    const [ex, ey] = unit(mx - Q.x, my - Q.y);
    const p0 = [P.x + sx * R, P.y + sy * R], p2 = [Q.x + ex * (R + 2), Q.y + ey * (R + 2)];
    const d = `M ${p0[0]} ${p0[1]} Q ${mx} ${my} ${p2[0]} ${p2[1]}`;
    const bx = 0.25 * p0[0] + 0.5 * mx + 0.25 * p2[0], by = 0.25 * p0[1] + 0.5 * my + 0.25 * p2[1];
    const lo = off === 0 ? 11 : 13 * Math.sign(off);
    let lx = bx + nx * lo, ly = by + ny * lo;
    if (off === 0 && Math.abs(uy) < 0.2) { lx = bx; ly = by - 9; }
    return { key: idx, d, color, dash, lx, ly: ly + 4, label, cls: e.cls };
  });
  const markerId = useMemo(() => 'arr' + Math.random().toString(36).slice(2, 8), []);
  const colors = ['var(--ink)', 'var(--marker)', 'var(--tick)', 'var(--biro)'];
  return (
    <div class="diagram">
      <svg viewBox={`${minX} ${minY} ${W} ${H}`} width={Math.min(W * 1.15, 760)} role="img" aria-label={title || 'State diagram'} style={{ maxHeight: height }}>
        <defs>
          {colors.map((c, i) => (
            <marker key={i} id={`${markerId}-${i}`} viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
              <path d="M 0 0 L 10 5 L 0 10 z" style={{ fill: c }} />
            </marker>
          ))}
        </defs>
        {/* start arrow */}
        {pos[start] && <path d={`M ${pos[start].x - R - 36} ${pos[start].y} L ${pos[start].x - R - 2} ${pos[start].y}`} style={{ stroke: 'var(--ink)', fill: 'none' }} stroke-width="1.6" marker-end={`url(#${markerId}-0)`} />}
        {items.filter(Boolean).map((it) => (
          <g key={it.key}>
            <path d={it.d} style={{ stroke: it.color, fill: 'none' }} stroke-width={it.cls ? 2 : 1.6} stroke-dasharray={it.dash} marker-end={`url(#${markerId}-${colors.indexOf(it.color)})`} />
            <text x={it.lx} y={it.ly} text-anchor="middle" font-size="15" style={{ fill: it.color, stroke: 'var(--paper)', strokeWidth: 4, paintOrder: 'stroke', fontStyle: 'normal' }}>{it.label}</text>
          </g>
        ))}
        {states.map((s) => pos[s] && (
          <g key={s}>
            <circle cx={pos[s].x} cy={pos[s].y} r={R} style={{ fill: highlight[s] || 'var(--paper)', stroke: 'var(--ink)' }} stroke-width="1.6" />
            {accept.includes(s) && <circle cx={pos[s].x} cy={pos[s].y} r={R - 4.5} style={{ fill: 'none', stroke: 'var(--ink)' }} stroke-width="1.3" />}
            <StateLabel name={String(s)} x={pos[s].x} y={pos[s].y} size={numeric ? 15 : 16} />
          </g>
        ))}
      </svg>
    </div>
  );
}

// ---------------------------------------------------------------- parse trees
export function layoutTree(root) {
  let leafX = 0;
  const nodes = [], links = [];
  (function walk(n, depth) {
    n._d = depth;
    if (!n.kids || !n.kids.length) { n._x = leafX++; }
    else {
      for (const k of n.kids) walk(k, depth + 1);
      n._x = (n.kids[0]._x + n.kids[n.kids.length - 1]._x) / 2;
    }
    nodes.push(n);
    if (n.kids) for (const k of n.kids) links.push([n, k]);
  })(root, 0);
  return { nodes, links, leaves: leafX, depth: Math.max(...nodes.map((n) => n._d)) };
}

export function ParseTree({ root, isVar = (s) => /^[A-Z]/.test(s), title }) {
  const { nodes, links, leaves, depth } = useMemo(() => layoutTree(structuredClone(strip(root))), [root]);
  const gx = 34, gy = 54, padX = 24, padY = 22;
  const W = Math.max(1, leaves) * gx + padX * 2, H = depth * gy + padY * 2 + 10;
  const X = (n) => padX + n._x * gx + gx / 2, Y = (n) => padY + n._d * gy + 8;
  return (
    <div class="diagram">
      <svg viewBox={`0 0 ${W} ${H}`} width={Math.min(W * 1.2, 760)} role="img" aria-label={title || 'Parse tree'}>
        {links.map(([a, b], i) => <line key={i} x1={X(a)} y1={Y(a) + 8} x2={X(b)} y2={Y(b) - 12} style={{ stroke: 'var(--ink-3)' }} stroke-width="1.3" />)}
        {nodes.map((n, i) => (
          <text key={i} x={X(n)} y={Y(n) + 5} text-anchor="middle" font-size="17"
            style={{ fill: n.lambda ? 'var(--ink-3)' : isVar(n.sym) ? 'var(--biro)' : 'var(--ink)', fontStyle: isVar(n.sym) || n.lambda ? 'italic' : 'normal', fontWeight: isVar(n.sym) ? 600 : 400 }}>{n.sym}</text>
        ))}
      </svg>
    </div>
  );
}
function strip(n) { return { sym: n.sym, lambda: n.lambda, kids: n.kids ? n.kids.map(strip) : null }; }

// TM transition edges ({from,to,labels}) to an Automaton.
export function NTMDiagram({ N, edges, states, title }) {
  const sts = states || Array.from({ length: N + 1 }, (_, i) => i);
  const names = sts.map(String);
  const es = edges.map((e) => ({ from: String(e.from), to: String(e.to), labels: e.labels, cls: e.cls }));
  return <Automaton states={names} start="0" accept={[String(N)]} edges={es} last={[String(N)]} numeric title={title || 'NTM state diagram'} />;
}
