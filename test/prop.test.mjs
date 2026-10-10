import test from 'node:test';
import assert from 'node:assert/strict';
import * as P from '../src/engines/prop.js';
import { checkStep, parseLawList, optionsAt, suggestLaws } from '../src/engines/laws.js';

const p = P.parse;

test('parse and print in lecturer style', () => {
  assert.equal(P.show(p('¬(¬p ∨ ¬(q ∨ r))')), '¬(¬p ∨ ¬(q ∨ r))');
  assert.equal(P.show(p('p ∨ ¬q ∧ r')), 'p ∨ (¬q ∧ r)');
  assert.equal(P.show(p('p & q & r')), 'p ∧ q ∧ r');
  assert.equal(P.show(p('p & (q & r)')), 'p ∧ (q ∧ r)');
  assert.equal(P.show(p('~p -> q <-> r')), '(¬p → q) ↔ r');
  assert.equal(P.show(p('(p nand p) nand ((q nand q) nand r)')), '(p ↑ p) ↑ ((q ↑ q) ↑ r)');
  assert.equal(P.show(p('p xor q')), 'p ⊕ q');
  assert.equal(P.show(p('T | F')), 'T ∨ F');
  assert.equal(P.showMin(p('p ∨ (¬q ∧ r)')), 'p ∨ ¬q ∧ r');
  assert.equal(P.showFull(p('p ∨ ¬q ∧ r → s')), '(p ∨ (¬q ∧ r)) → s');
});

test('parse errors are helpful', () => {
  assert.equal(P.tryParse('p ∧ ∧').ok, false);
  assert.match(P.tryParse('p q').error, /connective/);
  assert.match(P.tryParse('p ⇒ q').error, /→/);
  assert.match(P.tryParse('p ↑ q ∧ r').error, /brackets/);
  assert.equal(P.tryParse('(p ↑ q) ∧ r').ok, true);
  assert.match(P.tryParse('(p ∧ q').error, /closing/);
});

test('binding: left association and priorities', () => {
  assert.equal(P.key(p('p ∧ q ∧ r')), '((p∧q)∧r)');
  assert.equal(P.key(p('p ∨ q ∧ r')), '(p∨(q∧r))');
  assert.equal(P.key(p('p ⊕ q ∨ r')), '(p⊕(q∨r))');
  assert.equal(P.key(p('p → q ⊕ r')), '(p→(q⊕r))');
  assert.equal(P.key(p('p ↔ q → r')), '(p↔(q→r))');
  assert.ok(P.isFullyBracketed(p('(p ∨ (¬q ∧ r)) → s')));
  assert.ok(!P.isFullyBracketed(p('p ∨ ¬q ∧ r → s')));
});

test('truth table rows follow the course order', () => {
  const r = P.rows(['p', 'q', 'r']).map((e) => ['p', 'q', 'r'].map((v) => (e[v] ? 'T' : 'F')).join(''));
  assert.deepEqual(r, ['FFF', 'FFT', 'FTF', 'TFF', 'FTT', 'TFT', 'TTF', 'TTT']);
  const r2 = P.rows(['p', 'q']).map((e) => (e.p ? 'T' : 'F') + (e.q ? 'T' : 'F'));
  assert.deepEqual(r2, ['FF', 'FT', 'TF', 'TT']);
});

test('logical status', () => {
  const s = P.status(p('¬p → (q ∧ ¬r)'));
  assert.equal(s.label, 'satisfiable');
  assert.equal(P.status(p('¬(p ∧ q) ∨ (p → q)')).label, 'valid');
  assert.equal(P.status(p('(¬p ∧ ¬q) ∧ (q ∨ p)')).label, 'unsatisfiable');
  assert.equal(P.status(p('p ∨ (p → q)')).label, 'valid');
  assert.ok(P.equivalent(p('p ↔ q'), p('(p → q) ∧ (q → p)')).equiv);
  assert.ok(P.consequence(p('p ⊕ q'), p('p ∨ q')).holds);
  assert.ok(!P.consequence(p('(p ∨ q) ∧ p'), p('¬q')).holds);
});

test('full DNF from 2025 Q7 table', () => {
  const vs = ['p', 'q', 'r'];
  const vals = [false, false, true, false, false, false, true, true];
  const tt = P.rows(vs).map((env, i) => ({ env, value: vals[i] }));
  const d = P.fullDNF(tt, vs);
  assert.equal(P.show(d), '(¬p ∧ q ∧ ¬r) ∨ (p ∧ q ∧ ¬r) ∨ (p ∧ q ∧ r)');
});

test('law steps from the notes and past papers', () => {
  const ok = (a, b, laws) => checkStep(p(a), p(b), laws);
  assert.ok(ok('¬(¬p ∨ ¬(q ∨ r))', '(¬¬p) ∧ ¬¬(q ∨ r)', ['demorgan']).ok);
  assert.ok(ok('(¬¬p) ∧ ¬¬(q ∨ r)', 'p ∧ (q ∨ r)', ['dneg']).ok);
  assert.ok(ok('p ∧ (q ∨ r)', '(p ∧ q) ∨ (p ∧ r)', ['dist']).ok);
  assert.ok(ok('(p ∧ q) ∧ ¬q', 'p ∧ (q ∧ ¬q)', ['assoc']).ok);
  assert.ok(ok('p ∧ (q ∧ ¬q)', 'p ∧ F', ['excl']).ok);
  assert.ok(ok('p ∧ F', 'F', ['dom']).ok);
  // 2025 Q6
  assert.ok(ok('p ∨ (p → q)', 'p ∨ (¬p ∨ q)', ['cond']).ok);
  assert.ok(ok('p ∨ (¬p ∨ q)', '(p ∨ ¬p) ∨ q', ['assoc']).ok);
  assert.ok(ok('(p ∨ ¬p) ∨ q', 'T ∨ q', ['excl']).ok);
  const dom = ok('T ∨ q', 'T', ['dom']);
  assert.ok(dom.ok); assert.equal(dom.strict, false);
  // tut 7 Q2
  assert.ok(ok('¬q → ¬p', '¬¬q ∨ ¬p', ['cond']).ok);
  assert.ok(ok('¬¬q ∨ ¬p', 'q ∨ ¬p', ['dneg']).ok);
  assert.ok(ok('q ∨ ¬p', '¬p ∨ q', ['comm']).ok);
  assert.ok(ok('¬p ∨ q', 'p → q', ['cond']).ok);
  // combined De Morgan + double negation (tut 7 Q5 / 2025 Q8)
  assert.ok(ok('p ∨ (¬q ∧ r)', '¬(¬p ∧ ¬(¬q ∧ r))', ['demorgan', 'dneg']).ok);
  assert.ok(ok('p ↑ q', '¬(p ∧ q)', ['nand']).ok);
  assert.ok(ok('p', '¬¬p', ['dneg']).ok);
  assert.ok(ok('p', 'p ∧ T', ['ident']).ok);
  assert.ok(ok('F', 'q ∧ ¬q', ['excl']).ok);
});

test('law step failures explain themselves', () => {
  const r = checkStep(p('p ∧ (q ∨ r)'), p('(p ∧ q) ∨ (p ∧ r)'), ['demorgan']);
  assert.equal(r.ok, false); assert.equal(r.kind, 'wronglaw');
  assert.deepEqual(r.suggestion.ids, ['dist']);
  const r2 = checkStep(p('p ∧ q'), p('p ∨ q'), ['comm']);
  assert.equal(r2.kind, 'notequiv');
  const r3 = checkStep(p('p ∨ q'), p('q ∨ p'), []);
  assert.equal(r3.kind, 'nolaw');
});

test('law names parse', () => {
  assert.deepEqual(parseLawList('De Morgan, double negation').sort(), ['demorgan', 'dneg']);
  assert.deepEqual(parseLawList('conditional'), ['cond']);
  assert.deepEqual(parseLawList('bi-conditional'), ['bicond']);
  assert.deepEqual(parseLawList('Rule for NAND'), ['nand']);
  assert.deepEqual(parseLawList('excluded middle'), ['excl']);
});

test('options at a selected node', () => {
  const f = p('¬(p ∧ q)');
  const opts = optionsAt(f, []);
  assert.ok(opts.some((o) => o.law === 'demorgan' && P.show(o.result) === '¬p ∨ ¬q'));
  assert.ok(opts.some((o) => o.law === 'nand' && P.show(o.result) === 'p ↑ q'));
});

test('suggest laws', () => {
  assert.deepEqual(suggestLaws(p('p → q'), p('¬p ∨ q')).ids, ['cond']);
});
