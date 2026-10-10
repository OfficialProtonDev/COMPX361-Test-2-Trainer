import { useState, useMemo, useEffect, useRef } from 'preact/hooks';
import * as P from '../../engines/prop.js';
import { LAWS, LAW, LAW_SHEET, checkStep, optionsAt } from '../../engines/laws.js';
import { TARGETS, solutionSteps, checkRestricted, OPNAME } from '../../engines/nand.js';
import { FORMS, THEMES, makeArgument, falsify, validity } from '../../engines/argue.js';
import { Rng } from '../../engines/rng.js';
import { STATUS_BANK, EQUIV_BANK, LAW_BANK, NAND_BANK, DNF_SPECIAL } from '../../data/propbank.js';
import {
  MathText, Btn, Seg, Chip, Fb, MathField, Step, Options, DrillHeader, useSolve, useSeed, ModelAnswer, SolvedBanner, TF, cx, Collapse,
} from '../kit.jsx';

// ---------------------------------------------------------------- random WFFs
export function genWff(rng, vs, { min = 5, max = 10, ops = ['and', 'or', 'imp', 'and', 'or', 'imp', 'iff', 'xor'] } = {}) {
  for (let t = 0; t < 500; t++) {
    const build = (d) => {
      if (d <= 0 || (d < 3 && rng.chance(0.3))) {
        const v = P.V(rng.pick(vs));
        return rng.chance(0.3) ? P.Not(v) : v;
      }
      if (rng.chance(0.15)) return P.Not(build(d - 1));
      return P.Bin(rng.pick(ops), build(d - 1), build(d - 1));
    };
    const f = build(3);
    const sz = P.size(f);
    if (sz < min || sz > max) continue;
    if (P.vars(f).length !== vs.length) continue;
    if (P.show(f).includes('¬¬')) continue;
    return f;
  }
  return P.parse('(p → q) ∨ ¬p');
}

const sortedEnvText = (env, vs) => vs.map((v) => `${v} = ${TF(env[v])}`).join(', ');

// ---------------------------------------------------------------- interactive truth table
export function TruthTable({ vs, cols, cells, setCell, wrong, answerCols = [], highlightRows = [], onRowClick, readOnly, values }) {
  const rows = P.rows(vs);
  return (
    <div class="scroll-x">
      <table class="tt">
        <thead>
          <tr>
            {vs.map((v) => <th key={v}><i>{v}</i></th>)}
            {cols.map((c, j) => <th key={j} class={cx(answerCols.includes(j) && 'ans')}><MathText text={P.show(c)} /></th>)}
          </tr>
        </thead>
        <tbody>
          {rows.map((env, i) => (
            <tr key={i} class={cx(highlightRows.includes(i) && 'sel')} onClick={onRowClick ? () => onRowClick(i) : undefined} style={onRowClick ? { cursor: 'pointer' } : undefined}>
              {vs.map((v) => <td key={v} class="var">{TF(env[v])}</td>)}
              {cols.map((c, j) => {
                const k = `${j}-${i}`;
                const val = values ? TF(P.evaluate(c, env)) : cells[k] || '';
                const isWrong = wrong && wrong.has(k);
                return (
                  <td key={j} class={cx(!readOnly && 'cell', isWrong && 'wrong', answerCols.includes(j) && 'ans')}
                    tabIndex={readOnly ? undefined : 0} aria-label={`${P.show(c)}, row ${i + 1}`}
                    onClick={readOnly ? undefined : (e) => { e.stopPropagation(); setCell(k, val === '' ? 'T' : val === 'T' ? 'F' : ''); }}
                    onKeyDown={readOnly ? undefined : (e) => {
                      const key = e.key.toLowerCase();
                      if (key === 't' || key === '1') setCell(k, 'T');
                      else if (key === 'f' || key === '0') setCell(k, 'F');
                      else if (key === 'backspace' || key === 'delete' || key === ' ') { e.preventDefault(); setCell(k, ''); }
                    }}>{val}</td>
                );
              })}
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
}

function useTable(cols, rows) {
  const [cells, setCells] = useState({});
  const [wrong, setWrong] = useState(null);
  const setCell = (k, v) => { setCells((c) => ({ ...c, [k]: v })); setWrong(null); };
  const check = () => {
    const bad = new Set();
    let empty = 0;
    cols.forEach((c, j) => rows.forEach((env, i) => {
      const k = `${j}-${i}`;
      if (!cells[k]) empty++;
      else if (cells[k] !== TF(P.evaluate(c, env))) bad.add(k);
    }));
    setWrong(bad);
    return { bad: bad.size, empty };
  };
  const fillColumn = (j) => setCells((c) => { const n = { ...c }; rows.forEach((env, i) => { n[`${j}-${i}`] = TF(P.evaluate(cols[j], env)); }); return n; });
  const reset = () => { setCells({}); setWrong(null); };
  return { cells, setCell, wrong, check, fillColumn, reset };
}

// ---------------------------------------------------------------- drill: truth tables & status
export function TableDrill({ preset }) {
  const id = 'p-table';
  const [mode, setMode] = useState(preset?.table?.mode || 'status');
  const [src, setSrc] = useState('bank');
  const [seed, next] = useSeed(preset?.seed);
  const [customErr, setCustomErr] = useState(null);
  const [custom, setCustom] = useState('');
  const [customB, setCustomB] = useState('');
  const [customSet, setCustomSet] = useState(null);
  const prob = useMemo(() => {
    const rng = new Rng(seed);
    if (src === 'custom' && customSet) return customSet;
    if (preset?.table && seed === preset.seed && mode === preset.table.mode) {
      return preset.table.mode === 'equiv' ? { kind: 'equiv', a: P.parse(preset.table.a), b: P.parse(preset.table.b), src: preset.table.src } : { kind: 'status', a: P.parse(preset.table.a), src: preset.table.src };
    }
    if (mode === 'status') {
      if (src === 'bank') { const b = rng.pick(STATUS_BANK); return { kind: 'status', a: P.parse(b.f), src: b.src }; }
      const vs = rng.chance(0.55) ? ['p', 'q', 'r'] : ['p', 'q'];
      return { kind: 'status', a: genWff(rng, vs, { min: 5, max: vs.length === 3 ? 9 : 8 }), src: 'random' };
    }
    if (src === 'bank') { const b = rng.pick(EQUIV_BANK); return { kind: 'equiv', a: P.parse(b.a), b: P.parse(b.b), src: b.src }; }
    const vs = ['p', 'q'];
    const a = genWff(rng, vs, { min: 4, max: 7 });
    const b = rng.chance(0.5) ? genWff(rng, vs, { min: 4, max: 7 }) : alt(a, rng);
    return { kind: 'equiv', a, b, src: 'random' };
  }, [seed, mode, src, customSet]);

  const vs = useMemo(() => (prob.kind === 'status' ? P.vars(prob.a) : P.vars(prob.a, prob.b)), [prob]);
  const rows = useMemo(() => P.rows(vs), [vs]);
  const cols = useMemo(() => {
    if (prob.kind === 'status') return P.subformulas(prob.a);
    const ca = P.subformulas(prob.a), cb = P.subformulas(prob.b);
    const keys = new Set(ca.map(P.key));
    return [...ca, ...cb.filter((c) => !keys.has(P.key(c)))];
  }, [prob]);
  const ansCols = prob.kind === 'status' ? [cols.length - 1] : [cols.findIndex((c) => P.same(c, prob.a)), cols.findIndex((c) => P.same(c, prob.b))].filter((x) => x >= 0);
  const T = useTable(cols, rows);
  const S = useSolve(id, seed + mode + src);
  const [tableMsg, setTableMsg] = useState(null);
  const [tableDone, setTableDone] = useState(false);
  const [choice, setChoice] = useState(null);
  const [model, setModel] = useState(null);
  const [counter, setCounter] = useState(null);
  const [verdict, setVerdict] = useState(null);
  useEffect(() => { T.reset(); setTableMsg(null); setTableDone(false); setChoice(null); setModel(null); setCounter(null); setVerdict(null); }, [prob]);

  const st = useMemo(() => P.status(prob.a, vs), [prob, vs]);
  const relTruth = useMemo(() => {
    if (prob.kind !== 'equiv') return null;
    const eq = P.equivalent(prob.a, prob.b).equiv, ab = P.consequence(prob.a, prob.b).holds, ba = P.consequence(prob.b, prob.a).holds;
    return eq ? 'equiv' : ab ? 'conseq' : ba ? 'reverse' : 'neither';
  }, [prob]);

  const checkTable = () => {
    const r = T.check();
    if (r.empty) setTableMsg({ kind: 'hint', text: `${r.empty} cell${r.empty > 1 ? 's are' : ' is'} still empty. Click a cell (or type T / F in it).` });
    else if (r.bad) setTableMsg({ kind: 'bad', text: `${r.bad} cell${r.bad > 1 ? 's are' : ' is'} wrong (marked in red). Work each column from the columns to its left.` });
    else { setTableMsg({ kind: 'good', text: 'Every entry is right.' }); setTableDone(true); }
  };
  const revealTable = () => { cols.forEach((_, j) => T.fillColumn(j)); S.reveal(); setTableDone(true); setTableMsg({ kind: 'hint', text: 'Table filled in for you. Study how each column comes from earlier ones.' }); };

  const statusOpts = [['valid', 'Valid (a tautology): every valuation is a model'], ['satisfiable', 'Satisfiable but not valid'], ['unsatisfiable', 'Unsatisfiable (a contradiction): no models']];
  const relOpts = [['equiv', 'They are logically equivalent (P ⇔ Q)'], ['conseq', 'Q is a logical consequence of P (P ⇒ Q) but they are not equivalent'], ['reverse', 'P is a logical consequence of Q (Q ⇒ P) but they are not equivalent'], ['neither', 'Neither is a logical consequence of the other']];
  const needModel = prob.kind === 'status' && choice && choice !== 'unsatisfiable';
  const needCounter = prob.kind === 'status' && choice && choice !== 'valid';
  const checkVerdict = () => {
    if (prob.kind === 'status') {
      if (choice !== st.label) { setVerdict({ kind: 'bad', text: `Not quite. Look at the answer column: it has ${st.models.length} T and ${st.counterexamples.length} F.` }); return; }
      if (needModel && (model == null || !P.evaluate(prob.a, rows[model]))) { setVerdict({ kind: 'bad', text: 'Click a row where the formula is T to give a model.' }); return; }
      if (needCounter && (counter == null || P.evaluate(prob.a, rows[counter]))) { setVerdict({ kind: 'bad', text: 'Now give a counterexample: click a row where the formula is F (use the second picker).' }); return; }
      setVerdict({ kind: 'good', text: 'Correct.' }); S.finish();
    } else {
      if (choice !== relTruth) { setVerdict({ kind: 'bad', text: 'Compare the two answer columns row by row: where P is T, is Q always T? And the other way round?' }); return; }
      setVerdict({ kind: 'good', text: 'Correct.' }); S.finish();
    }
  };
  const modelLines = () => {
    if (prob.kind === 'status') {
      const out = [];
      if (st.valid) out.push(`Every row of the answer column is T, so P = ${P.show(prob.a)} is valid (a tautology), and so also satisfiable.`);
      else if (st.unsatisfiable) out.push(`Every row of the answer column is F, so P = ${P.show(prob.a)} is unsatisfiable (a contradiction): it has no models.`);
      else {
        out.push(`P is not a tautology, as ${sortedEnvText(st.counterexamples[0], vs)} is a counterexample.`);
        out.push(`P is satisfiable, as ${sortedEnvText(st.models[0], vs)} is a model.`);
      }
      return out;
    }
    const lines = [];
    if (relTruth === 'equiv') lines.push('The two answer columns agree in every row, so the formulas are logically equivalent.');
    else {
      const ab = P.consequence(prob.a, prob.b), ba = P.consequence(prob.b, prob.a);
      lines.push(ab.holds ? 'Wherever P is T, Q is T too, so P ⇒ Q.' : `P ⇏ Q: with ${sortedEnvText(ab.env, vs)}, P is T but Q is F.`);
      lines.push(ba.holds ? 'Wherever Q is T, P is T too, so Q ⇒ P.' : `Q ⇏ P: with ${sortedEnvText(ba.env, vs)}, Q is T but P is F.`);
    }
    return lines;
  };

  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Propositional logic · PROP2–PROP4" title="Truth tables, status and equivalence"
        sub="Fill in the truth table column by column (rows in the course order: by number of T's), then read off the answer. Click a cell to cycle T / F, or focus it and type T or F.">
        <Seg value={mode} onChange={(v) => { setMode(v); setCustomSet(null); }} label="Mode" options={[{ value: 'status', label: 'Logical status' }, { value: 'equiv', label: 'Equivalence / consequence' }]} />
        <Seg value={src} onChange={(v) => { setSrc(v); next(); }} label="Source" options={[{ value: 'bank', label: 'Notes & tests' }, { value: 'random', label: 'Random' }, { value: 'custom', label: 'Your own' }]} />
        <Btn onClick={next}>New formula</Btn>
      </DrillHeader>

      {src === 'custom' && (
        <div class="card stack">
          <MathField id="tt-custom-a" label={mode === 'status' ? 'Your WFF' : 'P'} value={custom} setValue={setCustom} placeholder="e.g. (p → q) ∧ ¬q → ¬p" />
          {mode === 'equiv' && <MathField id="tt-custom-b" label="Q" value={customB} setValue={setCustomB} placeholder="e.g. ¬q → ¬p" />}
          <div class="row"><Btn kind="primary" onClick={() => {
            const a = P.tryParse(custom); const b = mode === 'equiv' ? P.tryParse(customB) : { ok: true };
            if (!a.ok || !b.ok) { setCustomErr(a.error || b.error); return; }
            const nv = P.vars(a.ast, ...(b.ast ? [b.ast] : [])).length;
            if (nv > 4) { setCustomErr(`That has ${nv} variables; the table would need ${2 ** nv} rows. Use at most 4 variables.`); return; }
            setCustomErr(null);
            setCustomSet(mode === 'status' ? { kind: 'status', a: a.ast, src: 'yours' } : { kind: 'equiv', a: a.ast, b: b.ast, src: 'yours' });
          }}>Use this</Btn><span class="small faint">Up to 4 variables.</span></div>
          {customErr && <Fb kind="bad">{customErr}</Fb>}
        </div>
      )}

      <div class="question">
        <div class="qmeta"><Chip kind="src">{prob.src}</Chip></div>
        {prob.kind === 'status'
          ? <div class="qtext">Determine the logical status of <MathText text={`P = ${P.show(prob.a)}`} /> using a truth table: is it valid, satisfiable, or unsatisfiable? Give a model and/or counterexample.</div>
          : <div class="qtext">Use a truth table to decide how <MathText text={`P = ${P.show(prob.a)}`} /> and <MathText text={`Q = ${P.show(prob.b)}`} /> are related.</div>}
      </div>

      <div class="steps">
        <Step n={1} title="Fill in the truth table" state={tableDone ? (S.revealed ? 'revealed' : 'done') : 'active'}
          aside={<span class="small faint">{rows.length} rows · {cols.length} columns</span>}>
          <TruthTable vs={vs} cols={cols} cells={T.cells} setCell={T.setCell} wrong={T.wrong} answerCols={ansCols} />
          <div class="step-actions">
            <Btn kind="primary" onClick={checkTable}>Check table</Btn>
            <Btn kind="ghost" onClick={() => { const j = cols.findIndex((c, jj) => rows.some((env, i) => (T.cells[`${jj}-${i}`] || '') !== TF(P.evaluate(c, env)))); if (j >= 0) { T.fillColumn(j); S.reveal(); setTableMsg(null); } }}>Fill the next column for me</Btn>
            <Btn kind="ghost" onClick={revealTable}>Show the whole table</Btn>
          </div>
          {tableMsg && <Fb kind={tableMsg.kind}>{tableMsg.text}</Fb>}
        </Step>

        <Step n={2} title={prob.kind === 'status' ? 'Read off the logical status' : 'Decide the relationship'} state={!tableDone ? 'locked' : verdict?.kind === 'good' ? (S.revealed ? 'revealed' : 'done') : 'active'}>
          <Options options={(prob.kind === 'status' ? statusOpts : relOpts).map((o) => o[1])} picked={(prob.kind === 'status' ? statusOpts : relOpts).findIndex((o) => o[0] === choice)}
            onPick={(i) => { setChoice((prob.kind === 'status' ? statusOpts : relOpts)[i][0]); setVerdict(null); }} reveal={verdict?.kind === 'good'} correct={(prob.kind === 'status' ? statusOpts : relOpts).findIndex((o) => o[0] === (prob.kind === 'status' ? st.label : relTruth))} />
          {(needModel || needCounter) && (
            <div class="grid2">
              {needModel && <div class="panel stack-sm"><div class="label">A model (a row where P is T)</div>
                <div class="row">{rows.map((env, i) => P.evaluate(prob.a, env) || true ? <Btn sm key={i} kind={model === i ? 'primary' : ''} onClick={() => { setModel(i); setVerdict(null); }}>{vs.map((v) => TF(env[v])).join('')}</Btn> : null)}</div></div>}
              {needCounter && <div class="panel stack-sm"><div class="label">A counterexample (a row where P is F)</div>
                <div class="row">{rows.map((env, i) => <Btn sm key={i} kind={counter === i ? 'primary' : ''} onClick={() => { setCounter(i); setVerdict(null); }}>{vs.map((v) => TF(env[v])).join('')}</Btn>)}</div>
                <span class="small faint">Rows are written as values of {vs.join(', ')}.</span></div>}
            </div>
          )}
          <div class="step-actions"><Btn kind="primary" onClick={checkVerdict} disabled={!choice}>Check</Btn>
            <Btn kind="ghost" onClick={() => { S.reveal(); setChoice(prob.kind === 'status' ? st.label : relTruth); setVerdict({ kind: 'hint', text: 'Answer shown.' }); S.finish(); }}>Show answer</Btn></div>
          {verdict && <Fb kind={verdict.kind}>{verdict.text}</Fb>}
        </Step>
      </div>

      {S.solved && (
        <>
          <ModelAnswer lines={modelLines()} />
          <SolvedBanner clean={!S.revealed} onNext={next}>Try a random one next, or type your own.</SolvedBanner>
        </>
      )}
    </div>
  );
}

function alt(a, rng) {
  // a near-miss variant of a for equivalence questions
  const opts = optionsAt(a, []).filter((o) => o.law !== 'comm');
  if (opts.length && rng.chance(0.6)) return opts[0].result;
  if (a.t === 'bin') return P.Bin(a.op === 'and' ? 'or' : a.op === 'or' ? 'and' : a.op === 'imp' ? 'iff' : 'imp', a.a, a.b);
  return P.Not(a);
}

// ---------------------------------------------------------------- drill: law-by-law proofs
export function LawsDrill({ preset }) {
  const id = 'p-laws';
  const [exId, setExId] = useState(preset?.lawId || 't25-q6');
  const [customA, setCustomA] = useState('');
  const [customB, setCustomB] = useState('');
  const [customEx, setCustomEx] = useState(null);
  const ex = useMemo(() => (exId === 'custom' && customEx ? customEx : LAW_BANK.find((x) => x.id === exId) || LAW_BANK[0]), [exId, customEx]);
  const start = useMemo(() => P.parse(ex.a), [ex]);
  const goal = useMemo(() => P.parse(ex.b), [ex]);
  const [lines, setLines] = useState([]);
  const [input, setInput] = useState('');
  const [laws, setLaws] = useState([]);
  const [msg, setMsg] = useState(null);
  const [mode, setMode] = useState('type');
  const [sel, setSel] = useState(null);
  const S = useSolve(id, ex.id + (customEx ? customEx.a + customEx.b : ''));
  useEffect(() => { setLines([]); setInput(''); setLaws([]); setMsg(null); setSel(null); }, [ex]);
  const current = lines.length ? lines[lines.length - 1].f : start;
  const done = P.same(current, goal);
  useEffect(() => { if (done && lines.length) S.finish(); }, [done, lines.length]);

  const addLine = (f, ls) => {
    const r = checkStep(current, f, ls);
    if (!r.ok) { setMsg({ kind: r.kind === 'notequiv' ? 'bad' : 'hint', text: r.message }); return false; }
    setLines((L) => [...L, { f: P.strip(f), laws: ls, note: r.strict === false ? 'lenient' : null }]);
    setMsg({ kind: 'good', text: r.message });
    setInput(''); setLaws([]); setSel(null);
    return true;
  };
  const submit = () => {
    const p = P.tryParse(input);
    if (!p.ok) { setMsg({ kind: 'bad', text: p.error }); return; }
    addLine(p.ast, laws);
  };
  const hint = () => {
    S.reveal();
    if (!ex.path) { setMsg({ kind: 'hint', text: 'Laws that apply to the last line: ' + [...new Set(optionsAt(current, []).map((o) => o.lawName))].join(', ') + '. (Use Click mode to explore.)' }); return; }
    const idx = [P.parse(ex.a), ...ex.path.map((p) => P.parse(p[0]))].findIndex((f) => P.same(f, current));
    if (idx >= 0 && idx < ex.path.length) {
      const [f, ls] = ex.path[idx];
      setMsg({ kind: 'hint', text: `Next, try ${ls.map((l) => LAW[l].name).join(' + ')}, giving ${f}.` });
    } else setMsg({ kind: 'hint', text: 'You have left the worked path, which is fine. Laws that apply now: ' + [...new Set(optionsAt(current, []).map((o) => o.lawName))].join(', ') + '.' });
  };
  const opts = useMemo(() => (sel ? optionsAt(current, sel) : []), [current, sel]);

  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Propositional logic · PROP3" title="Law-by-law equivalence proofs"
        sub="Each line must follow from the previous one by the law(s) you quote. Applying the same law in several places at once is fine, as is combining De Morgan with Double Negation, as in the lecturer’s solutions.">
        <select class="input" style={{ width: 'auto', minWidth: '240px' }} value={exId} onChange={(e) => setExId(e.currentTarget.value)} aria-label="Exercise">
          {[1, 2, 3].map((l) => <optgroup key={l} label={['', 'Warm-up and past papers', 'Building up', 'Longer proofs'][l]}>{LAW_BANK.filter((x) => x.lvl === l).map((x) => <option key={x.id} value={x.id}>{`${x.a}  ⇔  ${x.b}`}</option>)}</optgroup>)}
          <option value="custom">Your own pair…</option>
        </select>
        <Seg value={mode} onChange={setMode} label="Input mode" options={[{ value: 'type', label: 'Type lines' }, { value: 'click', label: 'Click to apply' }]} />
      </DrillHeader>

      {exId === 'custom' && (
        <div class="card stack">
          <div class="grid2">
            <MathField id="law-ca" label="Start from P" value={customA} setValue={setCustomA} placeholder="e.g. ¬(p ∨ ¬q)" />
            <MathField id="law-cb" label="Reach Q (or T / F)" value={customB} setValue={setCustomB} placeholder="e.g. ¬p ∧ q" />
          </div>
          <div class="row"><Btn kind="primary" onClick={() => {
            const a = P.tryParse(customA), b = P.tryParse(customB);
            if (!a.ok || !b.ok) { setMsg({ kind: 'bad', text: (a.error || b.error) }); return; }
            if (!P.equivalent(a.ast, b.ast).equiv) { setMsg({ kind: 'bad', text: 'Those two formulas are not equivalent, so no proof exists. Check them with a truth table.' }); return; }
            setCustomEx({ id: 'custom', a: P.show(a.ast), b: P.show(b.ast), src: 'yours' });
          }}>Start proof</Btn></div>
        </div>
      )}

      <div class="question">
        <div class="qmeta"><Chip kind="src">{ex.src}</Chip></div>
        <div class="qtext">{ex.b === 'T' ? <>Use the laws of logical equivalence to show that <MathText text={ex.a} /> is valid (i.e. ⇔ T).</> : ex.b === 'F' ? <>Use the laws to show that <MathText text={ex.a} /> is unsatisfiable (i.e. ⇔ F).</> : <>Use the laws of logical equivalence to show that <MathText text={`${ex.a} ⇔ ${ex.b}`} />.</>}</div>
        <Collapse title="Laws of logical equivalence (as supplied in the test)"><LawSheet /></Collapse>
      </div>

      <div class="card stack">
        <div class="working">
          <div><MathText text={P.showFull(start)} /></div>
          {lines.map((l, i) => (
            <div key={i}>⇔ <MathText text={P.showFull(l.f)} /><span class="why">({l.laws.map((x) => LAW[x].name).join(', ')}){l.note ? ' · uses commutativity implicitly' : ''}</span></div>
          ))}
        </div>
        {!done && mode === 'type' && (
          <div class="stack">
            <MathField id="law-in" label="Next line" value={input} setValue={setInput} onEnter={submit} placeholder="Type the next formula" />
            <div class="field"><span class="label">Law(s) used</span>
              <div class="law-chips">{LAWS.filter((l) => !l.extra).map((l) => <button type="button" key={l.id} class={cx('law-chip', laws.includes(l.id) && 'on')} onClick={() => setLaws((L) => (L.includes(l.id) ? L.filter((x) => x !== l.id) : [...L, l.id]))}>{l.n}. {l.name}</button>)}</div>
            </div>
            <div class="step-actions">
              <Btn kind="primary" onClick={submit}>Add line</Btn>
              <Btn kind="ghost" onClick={hint}>Hint</Btn>
              {lines.length > 0 && <Btn kind="ghost" onClick={() => { setLines((L) => L.slice(0, -1)); setMsg(null); }}>Undo last line</Btn>}
            </div>
          </div>
        )}
        {!done && mode === 'click' && (
          <div class="stack">
            <div class="label">Click part of the last line to see which laws apply to it</div>
            <ClickFormula ast={current} sel={sel} onSel={setSel} />
            {sel && (opts.length ? (
              <div class="stack-sm">{opts.map((o, i) => (
                <button type="button" key={i} class="opt" onClick={() => addLine(o.result, [o.law])}>
                  <span class="chip blue">{o.lawName}</span><MathText text={P.show(o.result)} />
                </button>
              ))}</div>
            ) : <Fb kind="info">No law applies directly to that part. Select a bigger or smaller part.</Fb>)}
            <div class="step-actions">
              <Btn kind="ghost" onClick={hint}>Hint</Btn>
              {lines.length > 0 && <Btn kind="ghost" onClick={() => { setLines((L) => L.slice(0, -1)); setMsg(null); }}>Undo last line</Btn>}
            </div>
          </div>
        )}
        {msg && !done && <Fb kind={msg.kind}>{msg.text}</Fb>}
        {done && lines.length > 0 && <SolvedBanner clean={!S.revealed} onNext={() => { const i = LAW_BANK.findIndex((x) => x.id === exId); setExId(LAW_BANK[(i + 1) % LAW_BANK.length].id); }}>{`${lines.length} line${lines.length > 1 ? 's' : ''}. In a test, quote the law on every line, exactly like this.`}</SolvedBanner>}
      </div>
      {ex.path && (S.solved || S.revealed) && (
        <ModelAnswer title="A worked path" lines={[P.showFull(P.parse(ex.a)), ...ex.path.map(([f, ls]) => `  ⇔ ${P.showFull(P.parse(f))}   (${ls.map((l) => LAW[l].name).join(', ')})`)]} />
      )}
    </div>
  );
}

function ClickFormula({ ast, sel, onSel }) {
  const toks = P.showTokens(ast);
  const isSel = (path) => sel && path.length >= sel.length && sel.every((s, i) => path[i] === s);
  return (
    <div class="f block" style={{ fontSize: '24px' }}>
      {toks.map((t, i) => (
        <span key={i} class={cx('tok', isSel(t.path) && 'sel', t.kind === 'op' && 'op')} onClick={() => onSel(t.path)} role="button" tabIndex={0}
          onKeyDown={(e) => { if (e.key === 'Enter') onSel(t.path); }}>{t.kind === 'var' ? <i>{t.text}</i> : t.text}</span>
      ))}
    </div>
  );
}

export function LawSheet() {
  return (
    <div class="law-sheet">
      {LAW_SHEET.map(([n, fs], i) => (
        <div key={n}><div class="ln">{i + 1}. {n}</div>{fs.map((f) => <div key={f} class="lf"><MathText text={f} /></div>)}</div>
      ))}
    </div>
  );
}

// ---------------------------------------------------------------- drill: restricted connectives (NAND …)
export function NandDrill({ preset }) {
  const id = 'p-nand';
  const [src, setSrc] = useState('bank');
  const [seed, next] = useSeed(preset?.seed);
  const [target, setTarget] = useState('nand');
  const prob = useMemo(() => {
    const rng = new Rng(seed);
    if (preset?.nand && seed === preset.seed) return { f: P.parse(preset.nand.f), target: preset.nand.target, src: preset.nand.src };
    if (src === 'bank') { const b = rng.pick(NAND_BANK); return { f: P.parse(b.f), target: b.target, src: b.src }; }
    // a random formula that isn't already written with the allowed connectives
    let f;
    for (let t = 0; t < 50; t++) { f = genWff(rng, ['p', 'q'], { min: 3, max: 6, ops: ['and', 'or', 'imp', 'and', 'or'] }); if (!checkRestricted(f, f, target).ok) break; }
    return { f, target, src: 'random' };
  }, [seed, src, target, preset]);
  const [lines, setLines] = useState([]);
  const [input, setInput] = useState('');
  const [msg, setMsg] = useState(null);
  const S = useSolve(id, seed + src + target);
  useEffect(() => { setLines([]); setInput(''); setMsg(null); }, [prob]);
  const tgt = TARGETS[prob.target];
  const done = lines.length && checkRestricted(lines[lines.length - 1], prob.f, prob.target).ok;
  useEffect(() => { if (done) S.finish(); }, [done]);
  const add = () => {
    const p = P.tryParse(input);
    if (!p.ok) { setMsg({ kind: 'bad', text: p.error }); return; }
    const prev = lines.length ? lines[lines.length - 1] : prob.f;
    if (P.same(p.ast, prev)) { setMsg({ kind: 'hint', text: 'That’s the same as the line before. Rewrite part of it using one of the identities.' }); return; }
    const eq = P.equivalent(p.ast, prev);
    if (!eq.equiv) {
      const vs = P.vars(p.ast, prev);
      setMsg({ kind: 'bad', text: `Not equivalent to the previous line: with ${sortedEnvText(eq.env, vs)} the previous line is ${TF(eq.a)} but yours is ${TF(eq.b)}.` });
      return;
    }
    setLines((L) => [...L, P.strip(p.ast)]);
    setInput('');
    const r = checkRestricted(p.ast, prob.f, prob.target);
    setMsg(r.ok ? { kind: 'good', text: `Equivalent, and it only uses ${tgt.short}.` } : { kind: 'info', text: `Equivalent. Still uses ${r.bad.map((b) => OPNAME[b]).join(' ')}; keep going.` });
  };
  const sol = useMemo(() => solutionSteps(prob.f, prob.target), [prob]);
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Propositional logic · PROP5" title="Functional completeness: rewrite with fewer connectives"
        sub="Each line must be logically equivalent to the previous one; the last line may use only the allowed connectives. This is the 3–4 mark NAND question from 2023 and 2025.">
        <Seg value={src} onChange={(v) => { setSrc(v); next(); }} label="Source" options={[{ value: 'bank', label: 'Past papers & tutorials' }, { value: 'random', label: 'Random' }]} />
        {src === 'random' && <select class="input" style={{ width: 'auto' }} value={target} onChange={(e) => setTarget(e.currentTarget.value)} aria-label="Allowed connectives">{Object.entries(TARGETS).map(([k, t]) => <option key={k} value={k}>{t.label}</option>)}</select>}
        <Btn onClick={next}>New question</Btn>
      </DrillHeader>
      <div class="question">
        <div class="qmeta"><Chip kind="src">{prob.src}</Chip><Chip kind="blue">{tgt.label}</Chip></div>
        <div class="qtext">Give a WFF using <strong>{tgt.label}</strong> that is logically equivalent to <MathText text={`P = ${P.show(prob.f)}`} />, showing your reasoning.</div>
        <Collapse title="Useful identities">
          <div class="stack-sm">
            {prob.target === 'nand' && ['¬A ⇔ A ↑ A', 'A ↑ B ⇔ ¬(A ∧ B)   (rule for NAND)', 'A ∧ B ⇔ ¬(A ↑ B) ⇔ (A ↑ B) ↑ (A ↑ B)', 'A ∨ B ⇔ ¬(¬A ∧ ¬B) ⇔ (A ↑ A) ↑ (B ↑ B)'].map((x) => <MathText key={x} text={x} />)}
            {prob.target === 'nor' && ['¬A ⇔ A ↓ A', 'A ↓ B ⇔ ¬(A ∨ B)', 'A ∨ B ⇔ (A ↓ B) ↓ (A ↓ B)', 'A ∧ B ⇔ (A ↓ A) ↓ (B ↓ B)'].map((x) => <MathText key={x} text={x} />)}
            {prob.target === 'fimp' && ['¬A ⇔ A → F', 'A ∨ B ⇔ ¬A → B', 'A ∧ B ⇔ ¬(A → ¬B)'].map((x) => <MathText key={x} text={x} />)}
            {['notand', 'notor', 'notandor'].includes(prob.target) && ['A → B ⇔ ¬A ∨ B', 'A ↑ B ⇔ ¬(A ∧ B)', '¬(A ∧ B) ⇔ ¬A ∨ ¬B', '¬(A ∨ B) ⇔ ¬A ∧ ¬B'].map((x) => <MathText key={x} text={x} />)}
          </div>
        </Collapse>
      </div>
      <div class="card stack">
        <div class="working">
          <div><MathText text={`P = ${P.show(prob.f)}`} /></div>
          {lines.map((l, i) => <div key={i}>⇔ <MathText text={P.show(l)} /></div>)}
        </div>
        {!done && <>
          <MathField id="nand-in" label="Next line" value={input} setValue={setInput} onEnter={add} kind="nand" syms={prob.target === 'nand' ? 'nand' : 'prop'} placeholder={prob.target === 'nand' ? 'e.g. (p ↑ p) ↑ (q ↑ q)' : 'Next equivalent formula'} />
          <div class="step-actions"><Btn kind="primary" onClick={add}>Add line</Btn>
            <Btn kind="ghost" onClick={() => { S.reveal(); const nxt = sol.find((s) => !lines.some((l) => P.same(l, s.f)) && !P.same(s.f, prob.f)); if (nxt) setMsg({ kind: 'hint', text: `Try: ${P.show(nxt.f)}${nxt.why ? `   (${nxt.why})` : ''}` }); }}>Hint</Btn>
            {lines.length > 0 && <Btn kind="ghost" onClick={() => setLines((L) => L.slice(0, -1))}>Undo</Btn>}
            <span class="small faint">Tip: you can paste in the final answer directly.</span></div>
        </>}
        {msg && <Fb kind={msg.kind}>{msg.text}</Fb>}
        {done ? <SolvedBanner clean={!S.revealed} onNext={next}>Check the final line uses brackets around every ↑ / ↓ part.</SolvedBanner> : null}
      </div>
      {(S.solved || S.revealed) && <ModelAnswer lines={sol.map((s, i) => (i === 0 ? `P = ${P.show(s.f)}` : `  ⇔ ${P.show(s.f)}${s.why ? `     (${s.why})` : ''}`))} />}
    </div>
  );
}

// ---------------------------------------------------------------- drill: WFF from a truth table
export function DnfDrill({ preset }) {
  const id = 'p-dnf';
  const [seed, next] = useSeed(preset?.seed);
  const [src, setSrc] = useState(preset?.words ? 'words' : 'table');
  const prob = useMemo(() => {
    const rng = new Rng(seed);
    if (src === 'words') { const d = preset?.words && seed === preset.seed ? DNF_SPECIAL[0] : rng.pick(DNF_SPECIAL); return { desc: d.desc, target: P.parse(d.f), vs: d.vars, src: d.src }; }
    const vs = ['p', 'q', 'r'];
    const rs = P.rows(vs);
    let vals;
    if (preset?.vals && seed === preset.seed) vals = preset.vals;
    else do { const k = rng.int(2, 4); const on = new Set(rng.sample([...rs.keys()], k)); vals = rs.map((_, i) => on.has(i)); } while (vals.every((v) => !v));
    const tt = rs.map((env, i) => ({ env, value: vals[i] }));
    return { tt, vs, target: P.fullDNF(tt, vs), src: preset?.vals && seed === preset.seed ? '2025 Test 2 Q7' : '2025 Test 2 Q7 style' };
  }, [seed, src]);
  const [input, setInput] = useState('');
  const [msg, setMsg] = useState(null);
  const S = useSolve(id, seed + src);
  useEffect(() => { setInput(''); setMsg(null); }, [prob]);
  const check = () => {
    const p = P.tryParse(input);
    if (!p.ok) { setMsg({ kind: 'bad', text: p.error }); return; }
    const extra = P.vars(p.ast).filter((v) => !prob.vs.includes(v));
    if (extra.length) { setMsg({ kind: 'bad', text: `Only use ${prob.vs.join(', ')}.` }); return; }
    const eq = P.equivalent(p.ast, prob.target);
    if (!eq.equiv) { setMsg({ kind: 'bad', text: `Not quite: with ${sortedEnvText({ ...Object.fromEntries(prob.vs.map((v) => [v, false])), ...eq.env }, prob.vs)} your WFF is ${TF(eq.a)} but P should be ${TF(eq.b)}.` }); return; }
    setMsg({ kind: 'good', text: 'Correct: same truth value in every row.' });
    S.finish();
  };
  const full = useMemo(() => P.fullDNF(P.truthTable(prob.target, prob.vs), prob.vs), [prob]);
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Propositional logic · PROP5" title="Write a WFF with a given truth table"
        sub="Take one conjunction for each row where P is T (¬ on the variables that are F), and join them with ∨: a full DNF. Any equivalent WFF is accepted.">
        <Seg value={src} onChange={(v) => { setSrc(v); next(); }} label="Question type" options={[{ value: 'table', label: 'From a table' }, { value: 'words', label: 'From a description' }]} />
        <Btn onClick={next}>New question</Btn>
      </DrillHeader>
      <div class="question">
        <div class="qmeta"><Chip kind="src">{prob.src}</Chip><Chip kind="marks">1 mark</Chip></div>
        {prob.desc ? <div class="qtext">{prob.desc}</div> : <>
          <div class="qtext">Write down a WFF P involving p, q, r that has the following truth table.</div>
          <div class="scroll-x"><table class="tt"><thead><tr>{prob.vs.map((v) => <th key={v}><i>{v}</i></th>)}<th class="ans"><i>P</i></th></tr></thead>
            <tbody>{prob.tt.map((r, i) => <tr key={i}>{prob.vs.map((v) => <td key={v} class="var">{TF(r.env[v])}</td>)}<td class="ans">{TF(r.value)}</td></tr>)}</tbody></table></div>
        </>}
      </div>
      <div class="card stack">
        <MathField id="dnf-in" label="Your WFF" value={input} setValue={setInput} onEnter={check} placeholder="e.g. (¬p ∧ q ∧ ¬r) ∨ (p ∧ q ∧ r)" />
        <div class="step-actions"><Btn kind="primary" onClick={check}>Check</Btn><Btn kind="ghost" onClick={() => { S.reveal(); setInput(P.show(full)); }}>Show a full DNF</Btn></div>
        {msg && <Fb kind={msg.kind}>{msg.text}</Fb>}
        {S.solved && <SolvedBanner clean={!S.revealed} onNext={next} />}
      </div>
      {(S.solved || S.revealed) && <ModelAnswer lines={[`P ⇔ ${P.show(full)}`, ...(prob.desc ? [`(or more simply: P ⇔ ${P.show(prob.target)})`] : [])]} />}
    </div>
  );
}

// ---------------------------------------------------------------- drill: arguments
export function ArgueDrill({ preset }) {
  const id = 'p-argue';
  const [seed, next] = useSeed(preset?.seed);
  const arg = useMemo(() => {
    const rng = new Rng(seed);
    if (preset?.argue && seed === preset.seed) return makeArgument(FORMS.find((f) => f.id === 't23'), THEMES[0]);
    const form = rng.pick(FORMS);
    const theme = rng.pick(THEMES);
    return makeArgument(form, theme, rng.shuffle([0, 1, 2]));
  }, [seed, preset]);
  const theme = THEMES.find((t) => t.id === arg.theme);
  const S = useSolve(id, seed);
  // step 1: atoms
  const atomChoices = useMemo(() => {
    const rng = new Rng(seed + 7);
    const used = arg.atoms.map((a) => a.m);
    const negs = theme.atoms.filter((a) => used.includes(a.pos)).map((a) => a.neg);
    return rng.shuffle([...used.map((t) => ({ t, ok: true })), ...negs.map((t) => ({ t, ok: false }))]);
  }, [arg]);
  const [picked, setPicked] = useState([]);
  const [s1, setS1] = useState(null);
  const [tr, setTr] = useState({});
  const [trOk, setTrOk] = useState({});
  const [trMsg, setTrMsg] = useState({});
  const [wff, setWff] = useState('');
  const [wffMsg, setWffMsg] = useState(null);
  const [verdict, setVerdict] = useState(null);
  const [ce, setCe] = useState({});
  const [vMsg, setVMsg] = useState(null);
  const [shown, setShown] = useState(0);
  useEffect(() => { setPicked([]); setS1(null); setTr({}); setTrOk({}); setTrMsg({}); setWff(''); setWffMsg(null); setVerdict(null); setCe({}); setVMsg(null); setShown(0); }, [arg]);
  const sentences = [...arg.premEn.map((s, i) => ({ k: 'p' + i, label: `Premise ${i + 1}`, en: s, ast: arg.premAst[i] })), { k: 'c', label: 'Conclusion', en: arg.conclEn, ast: arg.conclAst }];
  const step1Done = s1?.kind === 'good';
  const step2Done = sentences.every((s) => trOk[s.k]);
  const step3Done = wffMsg?.kind === 'good';
  const fz = useMemo(() => falsify(arg.premAst, arg.conclAst), [arg]);
  const val = useMemo(() => validity(arg.premAst, arg.conclAst), [arg]);
  const letters = arg.atoms.map((a) => a.l);

  const check1 = () => {
    const ok = atomChoices.filter((c) => c.ok).map((c) => c.t);
    const pickedT = picked.map((i) => atomChoices[i].t);
    if (pickedT.length === ok.length && ok.every((t) => pickedT.includes(t))) setS1({ kind: 'good', text: 'Right: atomic propositions are positive statements; “not …” is written with ¬.' });
    else if (pickedT.some((t) => !ok.includes(t))) setS1({ kind: 'bad', text: 'A negative statement like “… not …” isn’t atomic: it is ¬ applied to an atom.' });
    else setS1({ kind: 'bad', text: 'You are missing an atomic proposition that appears in the argument.' });
  };
  const checkTr = (s) => {
    const p = P.tryParse(tr[s.k] || '');
    if (!p.ok) { setTrMsg((m) => ({ ...m, [s.k]: p.error })); return; }
    const bad = P.vars(p.ast).filter((v) => !letters.includes(v));
    if (bad.length) { setTrMsg((m) => ({ ...m, [s.k]: `Use the letters ${letters.join(', ')}.` })); return; }
    const eq = P.equivalent(p.ast, s.ast);
    if (eq.equiv) { setTrOk((o) => ({ ...o, [s.k]: true })); setTrMsg((m) => ({ ...m, [s.k]: null })); }
    else setTrMsg((m) => ({ ...m, [s.k]: 'That doesn’t say the same thing. Check “if … then …” order and where the “not” goes.' }));
  };
  const checkWff = () => {
    const p = P.tryParse(wff);
    if (!p.ok) { setWffMsg({ kind: 'bad', text: p.error }); return; }
    const f = p.ast;
    if (f.t !== 'bin' || f.op !== 'imp') { setWffMsg({ kind: 'bad', text: 'The WFF to test is (premise 1 ∧ premise 2 ∧ …) → conclusion; its main connective is →.' }); return; }
    const conj = arg.premAst.reduce((a, b) => P.And(a, b));
    if (!P.equivalent(f.a, conj).equiv || !P.equivalent(f.b, arg.conclAst).equiv) { setWffMsg({ kind: 'bad', text: 'Put all the premises, joined by ∧, on the left of →, and the conclusion on the right.' }); return; }
    setWffMsg({ kind: 'good', text: 'Yes: the argument is valid exactly when this WFF is a tautology.' });
  };
  const checkVerdict = () => {
    if (verdict === null) return;
    if (verdict !== val.valid) { setVMsg({ kind: 'bad', text: val.valid ? 'Try to make the WFF false: can every premise be T while the conclusion is F?' : 'There is a valuation that makes every premise T and the conclusion F. Find it.' }); return; }
    if (!val.valid) {
      const env = Object.fromEntries(letters.map((l) => [l, ce[l] === true]));
      const okCE = arg.premAst.every((pp) => P.evaluate(pp, env)) && !P.evaluate(arg.conclAst, env);
      if (!okCE) { setVMsg({ kind: 'bad', text: 'Correct verdict, but your valuation doesn’t make all premises T and the conclusion F. Adjust the switches.' }); return; }
    }
    setVMsg({ kind: 'good', text: val.valid ? 'Correct: it can’t be made false, so it is a tautology and the argument is valid.' : 'Correct: your valuation is a counterexample, so the argument is invalid.' });
    S.finish();
  };
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Propositional logic · PROP4" title="Is the argument valid?"
        sub="Express the argument in propositional logic, write down the WFF that is a tautology exactly when the argument is valid, then prove or refute it. This was a 6-mark question in 2023.">
        <Btn onClick={next}>New argument</Btn>
      </DrillHeader>
      <div class="question">
        <div class="qmeta"><Chip kind="marks">6 marks</Chip><Chip kind="src">{arg.form.id === 't23' && arg.theme === 'test' ? '2023 Test 2 Q5' : 'generated'}</Chip></div>
        <div class="qtext">For the following logical argument, carefully express it in terms of propositional logic by first defining suitable propositions, and write down a WFF which is a tautology if and only if the argument is valid, and hence prove or otherwise its validity.</div>
        <div class="panel" style={{ textAlign: 'center', fontSize: '16.5px' }}>
          {arg.premEn.map((s, i) => <div key={i}>“{s}”</div>)}
          <div><em>“{arg.conclEn.replace(/\.$/, '')}.”</em></div>
        </div>
      </div>
      <div class="steps">
        <Step n={1} title="Define the propositions" state={step1Done ? 'done' : 'active'}>
          <div class="small muted">Which of these are the atomic propositions you should name with letters?</div>
          <div class="stack-sm">{atomChoices.map((c, i) => (
            <button type="button" key={i} class={cx('opt', picked.includes(i) && 'picked', step1Done && c.ok && 'right')} onClick={() => !step1Done && setPicked((pk) => (pk.includes(i) ? pk.filter((x) => x !== i) : [...pk, i]))}>
              <span class="key">{picked.includes(i) ? '✓' : ''}</span><span>“{c.t}”</span>
            </button>
          ))}</div>
          {!step1Done && <div class="step-actions"><Btn kind="primary" onClick={check1}>Check</Btn></div>}
          {s1 && <Fb kind={s1.kind}>{s1.text}</Fb>}
          {step1Done && <div class="panel stack-sm">{arg.atoms.map((a) => <div key={a.l}>Let <MathText text={a.l} /> = “{a.m}”.</div>)}</div>}
        </Step>
        <Step n={2} title="Translate each line" state={!step1Done ? 'locked' : step2Done ? 'done' : 'active'}>
          {sentences.map((s) => (
            <div key={s.k} class="stack-sm">
              <div class="small"><strong>{s.label}:</strong> “{s.en}”</div>
              {trOk[s.k] ? <Fb kind="good"><MathText text={P.show(P.parse(tr[s.k]))} /></Fb> : <>
                <MathField id={`arg-${s.k}`} value={tr[s.k] || ''} setValue={(v) => setTr((t) => ({ ...t, [s.k]: typeof v === 'function' ? v(t[s.k] || '') : v }))} onEnter={() => checkTr(s)} placeholder={`use ${letters.join(', ')}`} />
                <div class="row"><Btn sm onClick={() => checkTr(s)}>Check</Btn><Btn sm kind="ghost" onClick={() => { S.reveal(); setTr((t) => ({ ...t, [s.k]: P.show(s.ast) })); }}>Show</Btn></div>
                {trMsg[s.k] && <div class="err">{trMsg[s.k]}</div>}
              </>}
            </div>
          ))}
        </Step>
        <Step n={3} title="The WFF to test" state={!step2Done ? 'locked' : step3Done ? 'done' : 'active'}>
          <MathField id="arg-wff" value={wff} setValue={setWff} onEnter={checkWff} placeholder="(premise 1 ∧ premise 2 ∧ …) → conclusion" />
          <div class="step-actions"><Btn kind="primary" onClick={checkWff}>Check</Btn><Btn kind="ghost" onClick={() => { S.reveal(); setWff(P.show(arg.wff)); }}>Show</Btn></div>
          {wffMsg && <Fb kind={wffMsg.kind}>{wffMsg.text}</Fb>}
        </Step>
        <Step n={4} title="Prove or refute" state={!step3Done ? 'locked' : vMsg?.kind === 'good' ? 'done' : 'active'}>
          <Seg value={verdict} onChange={(v) => { setVerdict(v); setVMsg(null); }} label="Verdict" options={[{ value: true, label: 'Valid (tautology)' }, { value: false, label: 'Invalid' }]} />
          {verdict === false && (
            <div class="panel stack-sm"><div class="label">Counterexample: set each proposition</div>
              <div class="row">{letters.map((l) => <Btn sm key={l} kind={ce[l] ? 'primary' : ''} onClick={() => setCe((c) => ({ ...c, [l]: !c[l] }))}><i>{l}</i>&nbsp;= {ce[l] ? 'T' : 'F'}</Btn>)}</div></div>
          )}
          <div class="step-actions"><Btn kind="primary" onClick={checkVerdict} disabled={verdict === null}>Check</Btn>
            <Btn kind="ghost" onClick={() => { S.reveal(); setShown(fz.lines.length); }}>Show the “make it false” reasoning</Btn></div>
          {vMsg && <Fb kind={vMsg.kind}>{vMsg.text}</Fb>}
          {shown > 0 && <div class="model">{fz.lines.slice(0, shown).map((l, i) => <div key={i} class="model-line"><MathText text={l} /></div>)}</div>}
        </Step>
      </div>
      {S.solved && (
        <ModelAnswer lines={[
          ...arg.atoms.map((a) => `Let ${a.l} = “${a.m}”.`),
          `The argument is: ${arg.premAst.map((x) => P.show(x)).join(',  ')}  ∴ ${P.show(arg.conclAst)}.`,
          `It is valid iff this WFF is a tautology:  ${P.show(arg.wff)}.`,
          ...fz.lines,
        ]} />
      )}
      {S.solved && <SolvedBanner clean={!S.revealed} onNext={next}>{arg.form.name}: {arg.form.valid ? 'valid' : 'invalid'} form.</SolvedBanner>}
    </div>
  );
}

// ---------------------------------------------------------------- drill: binding priority
export function BindDrill() {
  const id = 'p-bind';
  const [seed, next] = useSeed();
  const f = useMemo(() => {
    const rng = new Rng(seed);
    for (let t = 0; t < 200; t++) {
      const g = genWff(rng, rng.pick([['p', 'q', 'r'], ['p', 'q', 'r', 's']]), { min: 6, max: 10, ops: ['and', 'or', 'imp', 'iff', 'xor', 'and', 'or', 'imp'] });
      const m = P.showMin(g);
      if (m !== P.showFull(g) && (m.match(/[∧∨→↔⊕]/g) || []).length >= 3) return g;
    }
    return P.parse('p ∨ ¬q ∧ r → s');
  }, [seed]);
  const [input, setInput] = useState('');
  const [main, setMain] = useState(null);
  const [msg, setMsg] = useState(null);
  const [streak, setStreak] = useState(0);
  const S = useSolve(id, seed);
  useEffect(() => { setInput(''); setMain(null); setMsg(null); }, [f]);
  const ops = ['∧', '∨', '⊕', '→', '↔'];
  const check = () => {
    const mainOk = main === P.SYM[f.op];
    const p = P.tryParse(input);
    if (!mainOk) { setMsg({ kind: 'bad', text: 'Wrong main connective. The main connective is the one with the lowest priority (¬, ∧, ∨, ⊕, →, ↔ from highest to lowest); ties bind to the left.' }); setStreak(0); return; }
    if (!p.ok) { setMsg({ kind: 'bad', text: p.error }); return; }
    if (!P.isFullyBracketed(p.ast)) { setMsg({ kind: 'hint', text: 'Bracket every binary sub-formula (everything except the whole formula).' }); return; }
    if (!P.same(p.ast, f)) { setMsg({ kind: 'bad', text: `Your brackets change the meaning. Compare with the priority order.` }); setStreak(0); return; }
    setMsg({ kind: 'good', text: 'Correct.' }); setStreak((s) => s + 1); S.finish();
  };
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Propositional logic · PROP2" title="Binding priority" sub="Binding priority, highest first: ¬, ∧, ∨, ⊕, →, ↔. One connective repeated binds to the left: p ∧ q ∧ r means (p ∧ q) ∧ r.">
        <Btn onClick={next}>New formula</Btn>{streak > 1 && <Chip kind="good">{streak} in a row</Chip>}
      </DrillHeader>
      <div class="question"><div class="qtext">Insert all the brackets in <MathText text={P.showMin(f)} />, and name its main connective.</div></div>
      <div class="card stack">
        <div class="field"><span class="label">Main connective</span><div class="row">{ops.map((o) => <Btn key={o} kind={main === o ? 'primary' : ''} onClick={() => setMain(o)}><span class="f">{o}</span></Btn>)}</div></div>
        <MathField id="bind-in" label="Fully bracketed" value={input} setValue={setInput} onEnter={check} placeholder="Retype it with brackets" hidePreview />
        <div class="step-actions"><Btn kind="primary" onClick={check}>Check</Btn><Btn kind="ghost" onClick={() => { S.reveal(); setInput(P.showFull(f)); setMain(P.SYM[f.op]); }}>Show</Btn></div>
        {msg && <Fb kind={msg.kind}>{msg.text}</Fb>}
        {S.solved && <SolvedBanner clean={!S.revealed} onNext={next} />}
      </div>
    </div>
  );
}
