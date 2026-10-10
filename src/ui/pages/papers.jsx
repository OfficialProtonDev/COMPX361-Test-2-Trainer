import { useState, useMemo } from 'preact/hooks';
import { PAPERS, TUTORIALS } from '../../data/papers.js';
import * as G from '../../engines/gram.js';
import * as M from '../../engines/automata.js';
import * as P from '../../engines/prop.js';
import { Automaton, ParseTree, NTMDiagram } from '../render.jsx';
import { MathText, Btn, Seg, Chip, Fb, TF, cx } from '../kit.jsx';
import { DRILLS } from '../registry.jsx';

const T24 = { states: ['q0', 'q1', 'q2'], start: 'q0', accept: ['q2'], edges: [{ from: 'q0', to: 'q0', label: 'a' }, { from: 'q0', to: 'q1', label: 'b' }, { from: 'q1', to: 'q0', label: 'a' }, { from: 'q1', to: 'q2', label: 'b' }, { from: 'q2', to: 'q2', label: 'b' }, { from: 'q2', to: 'q0', label: 'a' }] };
const T25 = M.fromDelta(['q0', 'q1', 'q2', 'q3'], ['a', 'b'], { q0: { a: 'q1', b: 'q2' }, q1: { a: 'q1', b: 'q2' }, q2: { a: 'q3', b: 'q2' }, q3: { a: 'q3', b: 'q1' } }, 'q0', ['q3']);

export function Visual({ v }) {
  if (!v) return null;
  if (v.type === 'bits') return <div class="bits">{v.bits.split(' ').map((b, i) => <span key={i} class="bitcode">{b}</span>)}</div>;
  if (v.type === 'delta') return (
    <div class="scroll-x"><table class="tt"><thead><tr><th>δ</th>{v.cols.map((c) => <th key={c}>{c}</th>)}</tr></thead>
      <tbody>{v.rows.map((r) => <tr key={r[0]}>{r.map((c, i) => <td key={i} class={i === 0 ? 'var' : ''}><MathText text={c} /></td>)}</tr>)}</tbody></table></div>
  );
  if (v.type === 'dfsa') { const m = v.key === 't24' ? T24 : T25; return <Automaton states={m.states} start={m.start} accept={m.accept} edges={M.mergedEdges(m)} />; }
  if (v.type === 'tt') {
    const vs = ['p', 'q', 'r'];
    return (
      <div class="scroll-x"><table class="tt"><thead><tr>{vs.map((x) => <th key={x}><i>{x}</i></th>)}<th class="ans"><i>P</i></th></tr></thead>
        <tbody>{P.rows(vs).map((env, i) => <tr key={i}>{vs.map((x) => <td key={x} class="var">{TF(env[x])}</td>)}<td class="ans">{TF(v.vals[i])}</td></tr>)}</tbody></table></div>
    );
  }
  if (v.type === 'ntm') return <NTMDiagram N={v.N} states={v.states} edges={v.edges} />;
  if (v.type === 'tree' || v.type === 'nfsa+tree') {
    const g = G.parseGrammar(v.grammar).g;
    const forms = G.parseDerivation(v.deriv, g);
    const tree = G.treeFromForms(g, forms);
    const nfa = v.type === 'nfsa+tree' ? M.grammarToNFSA(g) : null;
    return (
      <div class="stack">
        {nfa && <Automaton states={nfa.states} start={nfa.start} accept={nfa.accept} edges={M.mergedEdges(nfa)} last={['Qf']} pos={v.pos} />}
        {tree && <ParseTree root={tree} isVar={(s) => g.V.includes(s)} />}
      </div>
    );
  }
  return null;
}

function Item({ it }) {
  const [open, setOpen] = useState(false);
  const d = it.drill && DRILLS[it.drill];
  return (
    <div class="qblock">
      <div class="row" style={{ alignItems: 'baseline' }}>
        <span class="qnum">{it.n}.</span>
        {it.marks != null && <Chip kind="marks">{it.marks} mark{it.marks === 1 ? '' : 's'}</Chip>}
        <span class="spacer" />
        {d && <Btn sm kind="primary" onClick={() => window.__openDrill(it.drill, it.preset)}>Practise: {d.title}</Btn>}
      </div>
      <div class="qtext"><MathText text={it.q} /></div>
      {it.vis && <Visual v={it.vis} />}
      <details class="sol" open={open} onToggle={(e) => setOpen(e.currentTarget.open)}>
        <summary>Official solution</summary>
        <div>
          {it.sol.map((l, i) => <div key={i} class="model-line" style={{ fontFamily: 'var(--font-math)', fontSize: '17px' }}><MathText text={l} /></div>)}
          {open && it.solVis && <Visual v={it.solVis} />}
          {it.notes && <Fb kind="hint">{it.notes}</Fb>}
        </div>
      </details>
    </div>
  );
}

export function PapersPage({ preset }) {
  // The overview can open a particular paper or tutorial ({ tab: '2024' }).
  const [tab, setTab] = useState(() => ([...PAPERS, ...TUTORIALS].some((p) => p.id === preset?.tab) ? preset.tab : '2025'));
  const paper = PAPERS.find((p) => p.id === tab);
  const tut = TUTORIALS.find((t) => t.id === tab);
  return (
    <div class="sheet">
      <header class="stack-sm">
        <div class="h-kicker">Past papers · official solutions</div>
        <h1 class="h-title">Past Test 2 papers and tutorials</h1>
        <p class="h-sub">Every question with the lecturer’s own solution (typed for 2024–25; transcribed from the handwritten 2023 and tutorial solutions, with his mark allocations in brackets). “Practise” opens the matching drill, preloaded with that exact question where possible. Earlier years’ scope may differ slightly from this year’s.</p>
        <div class="row" style={{ marginTop: '6px' }}>
          <Seg value={tab} onChange={setTab} label="Paper" options={[...PAPERS.map((p) => ({ value: p.id, label: p.title })), ...TUTORIALS.map((t) => ({ value: t.id, label: t.title.replace(/ \(.*\)/, '') }))]} />
        </div>
      </header>
      <div class="card">
        {paper && (
          <>
            <div class="row"><h2 class="h2">{paper.title}</h2><span class="small faint">{paper.date} · 60 minutes · {paper.total} marks</span></div>
            {paper.items.map((it) => <Item key={tab + it.n} it={it} />)}
          </>
        )}
        {tut && (
          <>
            <div class="row"><h2 class="h2">{tut.title}</h2></div>
            {tut.items.map((it) => <Item key={tab + it.n} it={it} />)}
          </>
        )}
      </div>
    </div>
  );
}
