// Mock tests: every generated paper totals 40, perfect answers earn every auto-marked mark,
// and blank answers earn nothing.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import * as esbuild from 'esbuild';
import os from 'node:os';
import path from 'node:path';
import * as G from '../src/engines/gram.js';
import * as P from '../src/engines/prop.js';
import { solutionSteps } from '../src/engines/nand.js';

const out = path.join(os.tmpdir(), `mock-bundle-${process.pid}.mjs`);
await esbuild.build({
  entryPoints: ['src/ui/pages/mock.jsx'], bundle: true, format: 'esm', platform: 'node', outfile: out,
  jsx: 'automatic', jsxImportSource: 'preact', loader: { '.js': 'jsx' }, logLevel: 'error',
});
const Mk = await import(out);

const derivText = (g, w) => G.findDerivation(g, w).map(G.formText).join(' ⇒ ');
function cellsFor(cols, vs, js) {
  const c = {};
  for (const j of js) P.rows(vs).forEach((env, i) => { c[`${j}-${i}`] = P.evaluate(cols[j], env) ? 'T' : 'F'; });
  return c;
}
function perfect(it) {
  const d = it.d;
  switch (it.kind) {
    case 'tm60': return { syms: d.dec.symbols.join(''), N: String(d.dec.N), edges: d.edges };
    case 'theory': return { text: d.t.model };
    case 'fa2reg': return { drawn: d.m.edges, gram: G.showProductions(d.g, '\n'), deriv: derivText(d.g, d.word) };
    case 'reg2nfsa': return { edges: d.nfa.edges, deriv: derivText(d.g, d.word) };
    case 'cfg': return { deriv: derivText(d.g, d.word), desc: d.opts ? d.opts.indexOf(d.b.desc) : undefined };
    case 'cs': return { text: 'S ⇒ 0A\n0A ⇒ 00A | 00' };
    case 'tf': return Object.fromEntries(d.qs.map((q, i) => ['t' + i, q.a]));
    case 'status': return { cells: cellsFor(d.cols, d.vs, [d.cols.length - 1]), status: d.st.label };
    case 'fc': return { cells: cellsFor(d.cols, d.vs, [d.ia, d.ib]), concl: 0, text: d.t.model };
    case 'dnf': return { f: P.show(d.target) };
    case 'nand': { const s = solutionSteps(d.f, 'nand'); return { final: P.show(s[s.length - 1].f) }; }
    case 'argue': return { text: 'answer' };
    case 'pred': return Object.fromEntries(d.partA.map((s, i) => ['a' + i, s.f]));
    case 'design': return { gram: d.t.model, deriv: derivText(d.model, d.word) };
    case 'ind': return d.terms ? Object.fromEntries(d.terms.map((t) => ['t' + t.i, t.v])) : { text: 'proof' };
    default: throw new Error('unknown kind ' + it.kind);
  }
}

for (const shape of Object.keys(Mk.SHAPES)) {
  test(`mock papers like ${shape}: 40 marks, perfect answers get every auto mark, blanks get none`, () => {
    for (let k = 1; k <= (Number(process.env.MOCK_N) || 40); k++) {
      const seed = (k * 2654435761) >>> 0;
      const paper = Mk.genPaper(seed, shape);
      assert.equal(paper.total, 40);
      const ans = {};
      for (const it of paper.items) ans[it.n] = perfect(it);
      for (const m of Mk.markPaper(paper, { ans })) {
        const autoMax = m.auto.reduce((s, p) => s + p.max, 0) + m.written.reduce((s, w) => s + w.marks, 0) + m.self.reduce((s, x) => s + x.marks, 0);
        assert.equal(autoMax, m.it.marks, `${shape} Q${m.it.n} (${m.it.kind}) parts add up to the question's marks`);
        for (const p of m.auto) assert.equal(p.got, p.max, `${shape} seed ${seed} Q${m.it.n} (${m.it.kind}) ${p.label}: ${p.note}`);
      }
      for (const m of Mk.markPaper(paper, { ans: {} })) assert.equal(m.got, 0, `${shape} seed ${seed} Q${m.it.n} blank`);
    }
  });
}

test('wrong answers lose marks with a reason', () => {
  const paper = Mk.genPaper(12345, '2025');
  const ans = {};
  for (const it of paper.items) ans[it.n] = perfect(it);
  const q1 = paper.items.find((it) => it.kind === 'tm60');
  ans[q1.n] = { ...ans[q1.n], N: String(q1.d.dec.N + 1), edges: q1.d.edges.slice(1) };
  const q8 = paper.items.find((it) => it.kind === 'nand');
  ans[q8.n] = { final: P.show(q8.d.f) };
  let m = Mk.markPaper(paper, { ans });
  const m1 = m.find((x) => x.it.n === q1.n);
  assert.ok(m1.got < q1.marks && m1.got > 0);
  assert.equal(m.find((x) => x.it.n === q8.n).got, 0, 'copying P earns nothing');
  // only ¬ left to replace earns 1
  const steps = solutionSteps(q8.d.f, 'nand').map((x) => x.f);
  const nearly = steps.find((f) => { const c = [...P.connectives(f)]; return c.includes('nand') && c.includes('not') && c.every((x) => x === 'nand' || x === 'not'); });
  if (nearly) {
    ans[q8.n] = { final: P.show(nearly) };
    m = Mk.markPaper(paper, { ans });
    assert.equal(m.find((x) => x.it.n === q8.n).got, 1);
  }
});

test('a number inside a predicate answer is marked, not a crash', () => {
  for (let k = 1; k <= 30; k++) {
    const paper = Mk.genPaper((k * 7919) >>> 0, '2025');
    const q9 = paper.items.find((it) => it.kind === 'pred');
    const ans = { [q9.n]: { a0: '∃x ∃y : P(x, y) ∧ x = 1', a1: '∀x : P(x, 1)', a2: 'P(1, 2)' } };
    const m = Mk.markPaper(paper, { ans }).find((x) => x.it.n === q9.n);
    assert.equal(m.got, 0);
    assert.ok(m.auto.every((p) => /doesn’t name anything|couldn’t/i.test(p.note)), m.auto.map((p) => p.note).join(' | '));
  }
});
