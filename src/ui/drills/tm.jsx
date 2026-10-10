import { useState, useMemo, useEffect, useRef } from 'preact/hooks';
import { STANDALONE } from '../host.js';
import * as TM from '../../engines/tmcode.js';
import { runMoore, validateMoore, TUT5, MOORE_TARGETS, checkMooreDesign, randomMoore } from '../../engines/moore.js';
import { Rng } from '../../engines/rng.js';
import { THEORY, HALTING_PROOF } from '../../data/theory.js';
import { HIER_TF } from '../../data/grambank.js';
import { NTMDiagram, Automaton } from '../render.jsx';
import { MathText, Btn, Seg, Chip, Fb, Step, Options, DrillHeader, useSolve, useSeed, ModelAnswer, SolvedBanner, cx, Collapse } from '../kit.jsx';
import { WrittenAnswer } from '../marking.jsx';

export function CodeTable() {
  const rows = [['0', '1', '2', '3'], ['4', '5', '6', '7'], ['8', '9', 'b', '⊥'], ['L', 'R', ',', '/']];
  return (
    <div class="scroll-x"><table class="code"><thead><tr>{[0, 1, 2, 3].flatMap((i) => [<th key={'s' + i}>σ</th>, <th key={'c' + i}>code(σ)</th>])}</tr></thead>
      <tbody>{rows.map((r, i) => <tr key={i}>{r.flatMap((s) => [<td key={'a' + s} style={{ fontFamily: 'var(--font-math)', fontSize: '16px' }}>{s}</td>, <td key={'b' + s}>{TM.CODE[s]}</td>])}</tr>)}</tbody></table></div>
  );
}

const normSym = (c) => ({ x: '⊥', X: '⊥', u: '⊥', U: '⊥', '_': '⊥', B: 'b', l: 'L', r: 'R' }[c] || c);
const PALETTE = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'b', '⊥', 'L', 'R', ',', '/'];

export function SymbolEntry({ blocks, value, setValue, checked, correct }) {
  const ref = useRef(null);
  const chars = [...value.replace(/\s+/g, '')].map(normSym);
  return (
    <div class="stack">
      <div class="bits">
        {blocks.map((b, i) => {
          const c = chars[i];
          const ok = checked && c !== undefined ? c === correct[i] : null;
          return (
            <div key={i} class="bitblock">
              <span class="bitcode">{b}</span>
              <span class={cx('f', ok === true && 'status ok', ok === false && 'status bad')} style={{ fontSize: '20px', minHeight: '26px' }}>{c ?? '·'}</span>
            </div>
          );
        })}
      </div>
      <input ref={ref} class="input math" value={value} onInput={(e) => setValue(e.currentTarget.value)} placeholder="Type one symbol per block, e.g. 11/1,1/2,0/⊥" aria-label="Decoded symbols" />
      <div class="symbar">{PALETTE.map((s) => <button type="button" key={s} class="sym" onMouseDown={(e) => e.preventDefault()} onClick={() => { const el = ref.current; const v = value; const a = el?.selectionStart ?? v.length; setValue(v.slice(0, a) + s + v.slice(el?.selectionEnd ?? a)); requestAnimationFrame(() => { try { el.focus(); el.setSelectionRange(a + 1, a + 1); } catch { /* ignore */ } }); }}>{s}</button>)}
        <button type="button" class="sym wide" onClick={() => setValue(value.replace(/.$/u, ''))}>⌫</button></div>
      <div class="small faint">Tip: type x for ⊥.</div>
    </div>
  );
}

// ---------------------------------------------------------------- decode
const PAPER_CODES = {
  t24: { bits: '10001 10001 11111 10001 11110 10001 11111 10010 11110 10000 11111 11011', partial: true, src: '2024 Test 2 Q1' },
  t25: { bits: '10011 11111 10001 11110 10001 11111 10001 11110 11101 11111 11011 11111', partial: true, src: '2025 Test 2 Q1' },
  t5a: { bits: '10001 11111 11011 11111 11011 11111 11011', partial: false, src: 'Tutorial 5 Q1(a)' },
  t5d: { bits: '10001 11111 11011 11111 11011 11111 10010 11110 11010', partial: false, src: 'Tutorial 5 Q1(d)' },
};

function corrupt(ntm, rng) {
  // make an invalid code in one of the ways the tutorial expects
  const syms = TM.symbolsOf(ntm);
  const k = rng.int(0, 2);
  if (k === 0) { // reference a state above N
    const i = syms.findIndex((s, j) => /[0-9]/.test(s) && syms[j + 1] === ',');
    if (i >= 0) { syms[i] = String(Math.min(9, ntm.N + 1)); return { syms, why: 'refers to a state above the halt state' }; }
  }
  if (k === 1) { syms.push('/', '⊥'); return { syms, why: 'has the wrong number of instructions' }; }
  const i = syms.findIndex((s, j) => syms[j - 1] === ',');
  if (i >= 0) { syms[i] = ','; return { syms, why: 'has a malformed instruction' }; }
  syms.splice(-2, 2); return { syms, why: 'has the wrong number of instructions' };
}

export function DecodeDrill({ preset }) {
  const id = 'tm-decode';
  const [seed, next] = useSeed(preset?.seed);
  const [mode, setMode] = useState(preset?.code ? 'paper' : '60');
  const prob = useMemo(() => {
    const rng = new Rng(seed);
    if (mode === 'paper') {
      const key = preset?.code && seed === preset.seed ? preset.code : rng.pick(Object.keys(PAPER_CODES));
      const p = PAPER_CODES[key];
      return { bits: p.bits.replace(/\s+/g, ''), partial: p.partial, src: p.src };
    }
    if (mode === '60') {
      const ntm = TM.randomNTM(rng, { N: rng.pick([2, 3, 3, 4, 5, 10, 11, 12]), fill: 0.7 });
      return { bits: TM.first60(ntm), partial: true, src: 'generated (2024/2025 style)' };
    }
    const ntm = TM.randomNTM(rng, { N: rng.pick([1, 2]), fill: 0.5 });
    if (rng.chance(0.5)) { const c = corrupt(ntm, rng); return { bits: TM.bitsOf(c.syms), partial: false, src: 'generated (tutorial 5 style)' }; }
    return { bits: TM.encode(ntm), partial: false, src: 'generated (tutorial 5 style)' };
  }, [seed, mode, preset]);
  const dec = useMemo(() => TM.decode(prob.bits, { partial: prob.partial }), [prob]);
  const blocks = TM.blocksOf(prob.bits);
  const [syms, setSyms] = useState('');
  const [symChecked, setSymChecked] = useState(false);
  const [n, setN] = useState('');
  const [valid, setValid] = useState(null);
  const [rows, setRows] = useState({});
  const [msg, setMsg] = useState({});
  const [stage, setStage] = useState(1);
  const S = useSolve(id, seed + mode);
  useEffect(() => { setSyms(''); setSymChecked(false); setN(''); setValid(null); setRows({}); setMsg({}); setStage(1); }, [prob]);
  const correct = dec.symbols;
  const typed = [...syms.replace(/\s+/g, '')].map(normSym);
  const symOk = typed.length === correct.length && typed.every((c, i) => c === correct[i]);
  const isValid = prob.partial ? true : dec.complete;
  const instrs = dec.instructions;

  const checkSyms = () => {
    setSymChecked(true);
    if (typed.length !== correct.length) { setMsg({ s: { kind: 'bad', text: `There are ${correct.length} blocks, so ${correct.length} symbols (you have ${typed.length}).` } }); return; }
    const wrong = typed.filter((c, i) => c !== correct[i]).length;
    if (wrong) { setMsg({ s: { kind: 'bad', text: `${wrong} symbol${wrong > 1 ? 's are' : ' is'} wrong (marked red). Use the code table.` } }); return; }
    setMsg({ s: { kind: 'good', text: `So the list form is: ${correct.join('').replace(/,/g, ', ')}` } });
    setStage(2);
  };
  const checkStruct = () => {
    if (Number(n) !== dec.N) { setMsg((m) => ({ ...m, n: { kind: 'bad', text: 'The halt state N is the number before the first “/”. (Several digits form one number.)' } })); return; }
    if (!prob.partial) {
      if (valid === null) { setMsg((m) => ({ ...m, n: { kind: 'bad', text: 'Is it the code of an NTM?' } })); return; }
      if (valid !== isValid) { setMsg((m) => ({ ...m, n: { kind: 'bad', text: isValid ? 'Look again: every instruction is fine and there are exactly 3N of them.' : 'Look again: check the number of instructions (3 per non-halt state) and the states referred to.' } })); return; }
      if (!isValid) { setMsg((m) => ({ ...m, n: { kind: 'good', text: `Right: ${dec.errors[0]} So the string does not correspond to any NTM.` } })); setStage(4); S.finish(); return; }
    }
    setMsg((m) => ({ ...m, n: { kind: 'good', text: `Halt state ${dec.N}: the states are 0, 1, …, ${dec.N}. Each non-halt state has three instructions (reading 0, 1, b).` } }));
    setStage(3);
  };
  const reads = ['0', '1', 'b'];
  const checkRows = () => {
    for (const ins of instrs) {
      if (ins.unknown) continue;
      const r = rows[ins.idx] || {};
      if (Number(r.q) !== ins.state || r.r !== ins.read) { setMsg((m) => ({ ...m, t: { kind: 'bad', text: `Instruction ${ins.idx + 1} (“${ins.text}”) belongs to state ${ins.state} reading ${ins.read}: instructions go 3 per state, in the order 0, 1, b.` } })); return; }
    }
    setMsg((m) => ({ ...m, t: { kind: 'good', text: 'All instructions placed. Here is as much of the NTM as the bits determine.' } }));
    setStage(4); S.finish();
  };
  const edges = TM.edgesOf(dec.delta);
  const known = new Set([0, dec.N, ...edges.flatMap((e) => [e.from, e.to])]);
  const drawStates = [...known].sort((a, b) => a - b);
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Turing machines · TM3" title="Decode a Turing number"
        sub="Split the bits into 5-bit codes, translate with the table, then read the list: halt state N first, then 3 instructions for each state 0 … N − 1 (reading 0, 1, b), each “⊥” or “next state, action”.">
        <Seg value={mode} onChange={(v) => { setMode(v); next(); }} label="Question type" options={[{ value: '60', label: 'First 60 bits' }, { value: 'full', label: 'Valid code?' }, { value: 'paper', label: 'Past papers' }]} />
        <Btn onClick={next}>New number</Btn>
      </DrillHeader>
      <div class="question">
        <div class="qmeta"><Chip kind="src">{prob.src}</Chip><Chip kind="marks">4 marks</Chip></div>
        <div class="qtext">{prob.partial ? 'The first 60 bits of the Turing number in binary of an NTM are as follows. Using the table, draw as much as you can of the NTM, including the halt state.' : 'Decide whether this natural number (in binary) is the code of an NTM M. If so, draw M’s state diagram.'}</div>
        <div class="bits">{blocks.map((b, i) => <span key={i} class="bitcode">{b}</span>)}</div>
        <Collapse title="Code table (supplied in the test)" open={false}><CodeTable /></Collapse>
      </div>
      <div class="steps">
        <Step n={1} title="Translate each block" state={stage > 1 ? 'done' : 'active'}>
          <SymbolEntry blocks={blocks} value={syms} setValue={(v) => { setSyms(v); setSymChecked(false); }} checked={symChecked} correct={correct} />
          {stage === 1 && <div class="step-actions"><Btn kind="primary" onClick={checkSyms}>Check symbols</Btn><Btn kind="ghost" onClick={() => { S.reveal(); setSyms(correct.join('')); }}>Show</Btn></div>}
          {msg.s && <Fb kind={msg.s.kind}>{msg.s.text}</Fb>}
        </Step>
        <Step n={2} title={prob.partial ? 'Find the halt state' : 'Halt state and validity'} state={stage < 2 ? 'locked' : stage > 2 ? 'done' : 'active'}>
          <div class="row"><span>Halt state N =</span><input class="input tiny" value={n} onInput={(e) => setN(e.currentTarget.value)} aria-label="Halt state" /></div>
          {!prob.partial && <div class="row"><span>Is it the code of an NTM?</span><Seg value={valid} onChange={setValid} label="Valid" options={[{ value: true, label: 'Yes' }, { value: false, label: 'No' }]} /></div>}
          {stage === 2 && <div class="step-actions"><Btn kind="primary" onClick={checkStruct}>Check</Btn></div>}
          {msg.n && <Fb kind={msg.n.kind}>{msg.n.text}</Fb>}
        </Step>
        {isValid && (
          <Step n={3} title="Place each instruction" state={stage < 3 ? 'locked' : stage > 3 ? 'done' : 'active'}>
            <div class="scroll-x"><table class="plain" style={{ minWidth: '420px' }}><thead><tr><th>#</th><th>Instruction</th><th>In state</th><th>Reading</th><th>Meaning</th></tr></thead>
              <tbody>{instrs.map((ins) => {
                const r = rows[ins.idx] || {};
                return (
                  <tr key={ins.idx}>
                    <td class="nums">{ins.idx + 1}</td>
                    <td class="f">{ins.unknown ? <span class="faint">{ins.partialText || '(cut off)'}</span> : ins.text}</td>
                    <td>{ins.unknown ? '—' : <select class="input" style={{ width: '70px' }} value={r.q ?? ''} onChange={(e) => setRows((R) => ({ ...R, [ins.idx]: { ...r, q: e.currentTarget.value } }))}><option value="">?</option>{Array.from({ length: dec.N }, (_, q) => <option key={q} value={q}>{q}</option>)}</select>}</td>
                    <td>{ins.unknown ? '—' : <select class="input" style={{ width: '70px' }} value={r.r ?? ''} onChange={(e) => setRows((R) => ({ ...R, [ins.idx]: { ...r, r: e.currentTarget.value } }))}><option value="">?</option>{reads.map((x) => <option key={x}>{x}</option>)}</select>}</td>
                    <td class="small">{ins.unknown ? 'not determined' : ins.undefined ? 'undefined (no edge)' : `edge to state ${ins.to}, labelled ${ins.read}/${ins.act}`}</td>
                  </tr>
                );
              })}</tbody></table></div>
            {stage === 3 && <div class="step-actions"><Btn kind="primary" onClick={checkRows}>Check</Btn><Btn kind="ghost" onClick={() => { S.reveal(); const R = {}; for (const ins of instrs) if (!ins.unknown) R[ins.idx] = { q: String(ins.state), r: ins.read }; setRows(R); }}>Show</Btn></div>}
            {msg.t && <Fb kind={msg.t.kind}>{msg.t.text}</Fb>}
          </Step>
        )}
      </div>
      {stage >= 4 && isValid && (
        <>
          <div class="card stack">
            <div class="h-kicker">As much of the NTM as you can draw</div>
            <NTMDiagram N={dec.N} states={drawStates} edges={edges} />
            <div class="small muted">Start state 0, halt state {dec.N} (double circle). {prob.partial ? 'The instructions after the cut-off are unknown, so other edges may exist.' : ''} Edge labels are “read/action”: write a symbol (0, 1, b) or move (L, R).</div>
          </div>
          <SolvedBanner clean={!S.revealed} onNext={next} />
        </>
      )}
      {stage >= 4 && !isValid && <SolvedBanner clean={!S.revealed} onNext={next} />}
    </div>
  );
}

// ---------------------------------------------------------------- encode
export function EncodeDrill() {
  const id = 'tm-encode';
  const [seed, next] = useSeed();
  const ntm = useMemo(() => { const rng = new Rng(seed); return TM.randomNTM(rng, { N: rng.pick([1, 2, 2, 3]), fill: 0.55 }); }, [seed]);
  const syms = TM.symbolsOf(ntm);
  const bits = TM.encode(ntm);
  const edges = TM.edgesOf(ntm.delta);
  const [tbl, setTbl] = useState({});
  const [list, setList] = useState('');
  const [bin, setBin] = useState('');
  const [msg, setMsg] = useState({});
  const [stage, setStage] = useState(1);
  const S = useSolve(id, seed);
  useEffect(() => { setTbl({}); setList(''); setBin(''); setMsg({}); setStage(1); }, [ntm]);
  const reads = ['0', '1', 'b'];
  const cellText = (q, r) => { const t = ntm.delta[q][r]; return t ? `${t[0]},${t[1]}` : '⊥'; };
  const checkTbl = () => {
    for (let q = 0; q < ntm.N; q++) for (const r of reads) {
      const v = (tbl[`${q}${r}`] || '').replace(/\s+/g, '').replace(/^[xu_]$/i, '⊥').replace(/,([lr])$/, (_, m) => ',' + m.toUpperCase()).replace(/,B$/, ',b');
      if (v !== cellText(q, r)) { setMsg({ t: { kind: 'bad', text: `δ(${q}, ${r}) should be ${cellText(q, r) === '⊥' ? '⊥ (no edge reading ' + r + ')' : `(${cellText(q, r).replace(',', ', ')})`}.` } }); return; }
    }
    setMsg({ t: { kind: 'good', text: 'The δ table is right.' } }); setStage(2);
  };
  const checkList = () => {
    const v = [...list.replace(/\s+/g, '')].map(normSym).join('');
    if (v !== syms.join('')) { setMsg((m) => ({ ...m, l: { kind: 'bad', text: 'Not quite: N first, then for each state 0, 1, … the three instructions for reading 0, 1, b, separated by “/”.' } })); return; }
    setMsg((m) => ({ ...m, l: { kind: 'good', text: 'Right.' } })); setStage(3);
  };
  const want60 = bits.slice(0, 60);
  const wantBlocks = TM.blocksOf(want60).length;
  const checkBin = () => {
    const v = bin.replace(/\s+/g, '');
    if (v !== want60) {
      const got = TM.blocksOf(v), want = TM.blocksOf(want60);
      const bad = got.slice(0, want.length).findIndex((b, i) => b !== want[i]);
      let text;
      if (bad >= 0) text = `Block ${bad + 1} is wrong: it should encode “${syms[bad]}”.`;
      else if (got.length > want.length) text = bits.length > 60 ? `The first ${want.length} blocks are right; the question only asks for the first 60 bits, so stop there.` : `Too many blocks: this machine’s whole Turing number is only ${bits.length} bits (${want.length} blocks).`;
      else text = bits.length > 60 ? `Keep going: give the first 60 bits (12 blocks); you have ${got.length}.` : `Keep going: this machine’s whole Turing number is ${bits.length} bits (${want.length} blocks), so give all of it; you have ${got.length}.`;
      setMsg((m) => ({ ...m, b: { kind: 'bad', text } })); return;
    }
    setMsg((m) => ({ ...m, b: { kind: 'good', text: `Correct. The whole Turing number has ${bits.length} bits.` } })); S.finish();
  };
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Turing machines · TM3" title="Encode an NTM" sub="The reverse of decoding: δ table → list form → binary. Practising both directions makes the decoding question automatic.">
        <Btn onClick={next}>New machine</Btn>
      </DrillHeader>
      <div class="question">
        <div class="qtext">Give the Turing number of this NTM (start state 0, halt state {ntm.N}).</div>
        <NTMDiagram N={ntm.N} edges={edges} />
        <Collapse title="Code table"><CodeTable /></Collapse>
      </div>
      <div class="steps">
        <Step n={1} title="Fill in the δ table" state={stage > 1 ? 'done' : 'active'}>
          <div class="small muted">Write “state,action” (e.g. 2,R) or x for ⊥.</div>
          <div class="scroll-x"><table class="tt"><thead><tr><th>δ</th>{reads.map((r) => <th key={r}>{r}</th>)}</tr></thead>
            <tbody>{Array.from({ length: ntm.N }, (_, q) => <tr key={q}><td class="var">{q}</td>{reads.map((r) => <td key={r}><input class="input tiny" style={{ width: '70px' }} value={tbl[`${q}${r}`] || ''} onInput={(e) => setTbl((t) => ({ ...t, [`${q}${r}`]: e.currentTarget.value }))} aria-label={`delta ${q} ${r}`} /></td>)}</tr>)}</tbody></table></div>
          {stage === 1 && <div class="step-actions"><Btn kind="primary" onClick={checkTbl}>Check</Btn><Btn kind="ghost" onClick={() => { S.reveal(); const t = {}; for (let q = 0; q < ntm.N; q++) for (const r of reads) t[`${q}${r}`] = cellText(q, r); setTbl(t); }}>Show</Btn></div>}
          {msg.t && <Fb kind={msg.t.kind}>{msg.t.text}</Fb>}
        </Step>
        <Step n={2} title="List form" state={stage < 2 ? 'locked' : stage > 2 ? 'done' : 'active'}>
          <input class="input math" value={list} onInput={(e) => setList(e.currentTarget.value)} placeholder={`${ntm.N}/…`} aria-label="List form" />
          {stage === 2 && <div class="step-actions"><Btn kind="primary" onClick={checkList}>Check</Btn><Btn kind="ghost" onClick={() => { S.reveal(); setList(syms.join('')); }}>Show</Btn></div>}
          {msg.l && <Fb kind={msg.l.kind}>{msg.l.text}</Fb>}
        </Step>
        <Step n={3} title={bits.length > 60 ? 'First 60 bits' : `The Turing number (all ${bits.length} bits)`} state={stage < 3 ? 'locked' : S.solved ? 'done' : 'active'}>
          <input class="input code" value={bin} onInput={(e) => setBin(e.currentTarget.value)} placeholder="10001 11111 …" aria-label="Binary" />
          {!S.solved && <div class="step-actions"><Btn kind="primary" onClick={checkBin}>Check</Btn><Btn kind="ghost" onClick={() => { S.reveal(); setBin(TM.spaced(want60)); }}>Show</Btn></div>}
          {msg.b && <Fb kind={msg.b.kind}>{msg.b.text}</Fb>}
          {S.solved && <ModelAnswer title="Whole Turing number"><div class="bits">{TM.blocksOf(bits).map((b, i) => <span key={i} class="bitcode">{b}</span>)}</div></ModelAnswer>}
        </Step>
      </div>
      {S.solved && <SolvedBanner clean={!S.revealed} onNext={next} />}
    </div>
  );
}

// ---------------------------------------------------------------- theory
export function TheoryDrill({ preset }) {
  const id = 'tm-theory';
  const [tid, setTid] = useState(preset?.theory || 'halting');
  const t = THEORY.find((x) => x.id === tid) || THEORY[0];
  const S = useSolve(id, tid);
  const tfs = HIER_TF.filter((q) => /Turing|decid|Halting|grammar that can generate|predicate/.test(q.s));
  const [ans, setAns] = useState({});
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Turing machines · TM3, TM4, GRAM3" title="Explain it: halting problem, universal TMs, undecidability"
        sub={`These 3–4 mark explanations appear every year. Write your answer, then ${STANDALONE ? 'mark it' : 'have it marked'} against the model answer.`}>
        <Seg value={tid} onChange={setTid} label="Question" options={THEORY.map((x) => ({ value: x.id, label: x.title }))} />
      </DrillHeader>
      <div class="question"><div class="qmeta"><Chip kind="src">{t.src}</Chip><Chip kind="marks">{t.marks} mark{t.marks > 1 ? 's' : ''}</Chip></div><div class="qtext">{t.q}</div></div>
      <div class="card stack">
        <WrittenAnswer key={tid} id={`theory-${tid}`} splitNote="the trainer’s suggestion (the official solutions give no split)" question={t.q} marks={t.marks} model={t.model} scheme={t.scheme} notes={t.notes} rows={6}
          placeholder="Write it as you would in the test: what it is, whether it exists / is solvable, why it matters." onScore={(s) => { if (s >= t.marks) S.finish(); }} />
      </div>
      {tid === 'halting' && (
        <Collapse title="Background: how the proof in TM4 goes (not needed for the 4-mark answer)">
          <ol class="prose">{HALTING_PROOF.map((l, i) => <li key={i}><MathText text={l} /></li>)}</ol>
        </Collapse>
      )}
      <div class="card stack">
        <div class="h-kicker">Quick true / false (2024 Q9 style)</div>
        {tfs.map((q, i) => (
          <div key={i} class="stack-sm" style={{ paddingBottom: '8px', borderBottom: '1px dashed var(--rule)' }}>
            <div class="row"><span>{q.s}</span><span class="spacer" /><Chip kind="src">{q.src}</Chip></div>
            <div class="row">{[true, false].map((v) => <Btn key={String(v)} sm kind={ans[i] === v ? (v === q.a ? 'primary' : 'danger') : ''} onClick={() => ans[i] === undefined && setAns((a) => ({ ...a, [i]: v }))}>{v ? 'True' : 'False'}</Btn>)}
              {ans[i] !== undefined && <span class={cx('chip', ans[i] === q.a ? 'good' : 'bad')}>{ans[i] === q.a ? 'Right' : `No: ${q.a ? 'true' : 'false'}`}</span>}</div>
            {ans[i] !== undefined && <div class="small muted">{q.why}</div>}
          </div>
        ))}
      </div>
    </div>
  );
}

// ---------------------------------------------------------------- Moore machines
function MooreDiagram({ m, highlight }) {
  const edges = [];
  for (const q of m.states) for (const a of ['0', '1']) {
    const t = m.delta[q]?.[a];
    if (!t) continue;
    let e = edges.find((x) => x.from === q && x.to === t);
    if (!e) edges.push((e = { from: q, to: t, labels: [] }));
    e.labels.push(a);
  }
  const names = m.states.map((q) => (q === m.start ? q : `${q}`));
  return (
    <div class="stack-sm">
      <Automaton states={names} start={m.start} accept={[]} edges={edges} highlight={highlight} />
      <div class="small muted" style={{ textAlign: 'center' }}>{m.states.filter((q) => q !== m.start).map((q) => `g(${q}) = ${m.g[q] ?? '?'}`).join(',  ')}</div>
    </div>
  );
}

export function MooreDrill({ preset }) {
  const id = 'moore';
  const [tab, setTab] = useState(preset?.moore || 'trace');
  const [seed, next] = useSeed(preset?.seed);
  const prob = useMemo(() => {
    const rng = new Rng(seed);
    if (preset?.tut5 && seed === preset.seed) return { m: TUT5, w: '11010011', src: 'Tutorial 5 Q2(a)' };
    const m = rng.chance(0.35) ? TUT5 : randomMoore(rng);
    let w = ''; const L = rng.int(5, 8); for (let i = 0; i < L; i++) w += rng.pick(['0', '1']);
    if (m === TUT5 && rng.chance(0.5)) w = '11010011';
    return { m, w, src: m === TUT5 ? 'Tutorial 5 Q2 machine' : 'random' };
  }, [seed]);
  const run = useMemo(() => runMoore(prob.m, prob.w), [prob]);
  const [path, setPath] = useState('');
  const [out, setOut] = useState('');
  const [msg, setMsg] = useState(null);
  const S = useSolve(id, seed + tab);
  useEffect(() => { setPath(''); setOut(''); setMsg(null); }, [prob, tab]);
  const checkTrace = () => {
    const p = path.replace(/[₀-₉]/g, (d) => String(d.charCodeAt(0) - 0x2080)).split(/[\s,→>-]+/).filter(Boolean).map((x) => x.replace(/^Q/, 'q')).map((x) => (x.startsWith('q') ? x : 'q' + x));
    if (p.join(' ') !== run.path.join(' ')) {
      const bad = p.findIndex((x, i) => x !== run.path[i]);
      setMsg({ kind: 'bad', text: bad >= 0 ? `State ${bad + 1} of the sequence should be ${run.path[bad]}${bad > 0 ? ` (from ${run.path[bad - 1]} reading ${prob.w[bad - 1]})` : ' (start in q0)'}.` : `The sequence should have ${run.path.length} states (one more than the input length).` });
      return;
    }
    if (out.replace(/[\s,]/g, '') !== run.out) { setMsg({ kind: 'bad', text: 'The states are right, but the output is wrong: write g(state) for every state after q0.' }); return; }
    setMsg({ kind: 'good', text: 'Correct.' }); S.finish();
  };
  // design
  const [tid, setTid] = useState('swap');
  const target = MOORE_TARGETS.find((t) => t.id === tid);
  const [ns, setNs] = useState(3);
  const [dm, setDm] = useState({});
  const [dres, setDres] = useState(null);
  useEffect(() => { setDm({}); setDres(null); }, [tid, ns]);
  const states = Array.from({ length: ns }, (_, i) => 'q' + i);
  const built = { states, start: 'q0', delta: Object.fromEntries(states.map((q) => [q, { 0: dm[q + '0'] || '', 1: dm[q + '1'] || '' }])), g: Object.fromEntries(states.slice(1).map((q) => [q, dm['g' + q] || ''])) };
  const checkDesign = () => { const r = checkMooreDesign(built, target); setDres(r); if (r.ok) S.finish(); };
  return (
    <div class="sheet">
      <DrillHeader id={id} kicker="Tutorial 5 Q2" title="Moore machines"
        sub="Like a DFSA with no accepting states: on reading x the machine moves to state q and overwrites x with g(q). It can never move back into q₀, and g(q₀) is undefined.">
        <Seg value={tab} onChange={setTab} label="Exercise" options={[{ value: 'trace', label: 'Trace the output' }, { value: 'design', label: 'Design a machine' }]} />
        {tab === 'trace' && <Btn onClick={next}>New machine</Btn>}
      </DrillHeader>
      {tab === 'trace' ? (
        <>
          <div class="question"><div class="qmeta"><Chip kind="src">{prob.src}</Chip></div>
            <div class="qtext">Give the transition sequence and hence the output string for the input <strong class="f">{prob.w}</strong>.</div>
            <MooreDiagram m={prob.m} /></div>
          <div class="card stack">
            <label class="field"><span class="label">State sequence (q0 first)</span><input class="input code" value={path} onInput={(e) => setPath(e.currentTarget.value)} placeholder="q0 q2 q1 …" /></label>
            <label class="field"><span class="label">Output string</span><input class="input code" value={out} onInput={(e) => setOut(e.currentTarget.value)} placeholder={'?'.repeat(prob.w.length)} /></label>
            <div class="step-actions"><Btn kind="primary" onClick={checkTrace}>Check</Btn><Btn kind="ghost" onClick={() => { S.reveal(); setPath(run.path.join(' ')); setOut(run.out); }}>Show</Btn></div>
            {msg && <Fb kind={msg.kind}>{msg.text}</Fb>}
            {(S.solved || S.revealed) && <ModelAnswer lines={[run.path.map((q, i) => (i === 0 ? q : `→${prob.w[i - 1]} ${q}`)).join(' '), `Output = ${run.path.slice(1).map((q) => `g(${q})`).join('')} = ${run.out}`]} />}
            {S.solved && <SolvedBanner clean={!S.revealed} onNext={next} />}
          </div>
        </>
      ) : (
        <>
          <div class="question">
            <div class="row"><select class="input" style={{ width: 'auto' }} value={tid} onChange={(e) => setTid(e.currentTarget.value)} aria-label="Behaviour">{MOORE_TARGETS.map((t) => <option key={t.id} value={t.id}>{t.title}</option>)}</select></div>
            <div class="qtext">Construct a Moore machine over {'{'}0, 1{'}'}: {target.desc}</div>
          </div>
          <div class="card stack">
            <div class="row"><span>Number of states (including q0):</span>{[2, 3, 4, 5, 6].map((k) => <Btn key={k} sm kind={ns === k ? 'primary' : ''} onClick={() => setNs(k)}>{k}</Btn>)}</div>
            <div class="scroll-x"><table class="tt"><thead><tr><th>state</th><th>on 0 go to</th><th>on 1 go to</th><th>g(state)</th></tr></thead>
              <tbody>{states.map((q) => <tr key={q}><td class="var"><MathText text={q} /></td>
                {['0', '1'].map((a) => <td key={a}><select class="input" style={{ width: '76px' }} value={dm[q + a] || ''} onChange={(e) => setDm((d) => ({ ...d, [q + a]: e.currentTarget.value }))} aria-label={`delta ${q} ${a}`}><option value="">?</option>{states.slice(1).map((s) => <option key={s}>{s}</option>)}</select></td>)}
                <td>{q === 'q0' ? <span class="faint">undefined</span> : <select class="input" style={{ width: '64px' }} value={dm['g' + q] || ''} onChange={(e) => setDm((d) => ({ ...d, ['g' + q]: e.currentTarget.value }))} aria-label={`g ${q}`}><option value="">?</option><option>0</option><option>1</option></select>}</td></tr>)}</tbody></table></div>
            {validateMoore(built, ['0', '1']).length === 0 && <MooreDiagram m={built} />}
            <div class="step-actions"><Btn kind="primary" onClick={checkDesign}>Check machine</Btn><span class="small faint">{target.hint}</span></div>
            {dres && <Fb kind={dres.ok ? 'good' : 'bad'}>{dres.message}</Fb>}
          </div>
        </>
      )}
    </div>
  );
}
