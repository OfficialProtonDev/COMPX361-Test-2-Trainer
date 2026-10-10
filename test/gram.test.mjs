import test from 'node:test';
import assert from 'node:assert/strict';
import * as G from '../src/engines/gram.js';
import * as M from '../src/engines/automata.js';
import * as TM from '../src/engines/tmcode.js';
import { runMoore, TUT5, checkMooreDesign, MOORE_TARGETS } from '../src/engines/moore.js';
import { Rng } from '../src/engines/rng.js';

const gr = (t, o) => { const r = G.parseGrammar(t, o); assert.ok(r.ok, r.errors.join('; ')); return r.g; };

test('2023 Q2: regular grammar to NFSA and derivation', () => {
  const g = gr('S ⇒ 0A|1B|λ, A ⇒ 0A|1B|1, B ⇒ 1B|0A|0');
  assert.equal(G.classify(g).type, 'regular');
  const m = M.grammarToNFSA(g);
  const want = [['S', '0', 'A'], ['S', '1', 'B'], ['S', 'λ', 'Qf'], ['A', '0', 'A'], ['A', '1', 'B'], ['A', '1', 'Qf'], ['B', '1', 'B'], ['B', '0', 'A'], ['B', '0', 'Qf']]
    .map(([from, label, to]) => ({ from, label, to }));
  assert.ok(M.sameEdges(want, m.edges).same);
  const forms = G.parseDerivation('S ⇒ 0A ⇒ 00A ⇒ 001B ⇒ 0011B ⇒ 00110', g);
  assert.ok(G.checkDerivation(forms, g, '00110').ok);
  assert.ok(M.accepts(m, '00110'));
  assert.ok(M.accepts(m, ''));
  const tree = G.treeFromForms(g, forms);
  assert.equal(tree.sym, 'S');
  assert.equal(tree.kids.length, 2);
});

test('2023 Q3: design 0^n 1^2n', () => {
  const target = { alphabet: ['0', '1'], test: (w) => /^0*1*$/.test(w) && (w.match(/1/g) || []).length === 2 * (w.match(/0/g) || []).length, maxLen: 9 };
  assert.ok(G.checkDesign(gr('S ⇒ 0S11 | λ'), target).ok);
  const bad = G.checkDesign(gr('S ⇒ 0S1 | λ'), target);
  assert.equal(bad.ok, false); assert.equal(bad.extra, '01');
  assert.ok(bad.derivation);
  const bad2 = G.checkDesign(gr('S ⇒ 0S11 | 011'), target);
  assert.equal(bad2.missing, '');
});

test('2024 Q3 and 2025 Q3: automaton to regular grammar', () => {
  const m24 = { states: ['q0', 'q1', 'q2'], start: 'q0', accept: ['q2'], edges: [
    { from: 'q0', to: 'q0', label: 'a' }, { from: 'q0', to: 'q1', label: 'b' }, { from: 'q1', to: 'q0', label: 'a' },
    { from: 'q1', to: 'q2', label: 'b' }, { from: 'q2', to: 'q2', label: 'b' }, { from: 'q2', to: 'q0', label: 'a' }] };
  const g = M.automatonToGrammar(m24);
  assert.equal(G.showProductions(g), 'q0 ⇒ aq0 | bq1, q1 ⇒ aq0 | bq2 | b, q2 ⇒ bq2 | b | aq0');
  const m25 = M.fromDelta(['q0', 'q1', 'q2', 'q3'], ['a', 'b'], { q0: { a: 'q1', b: 'q2' }, q1: { a: 'q1', b: 'q2' }, q2: { a: 'q3', b: 'q2' }, q3: { a: 'q3', b: 'q1' } }, 'q0', ['q3']);
  const g25 = M.automatonToGrammar(m25);
  assert.equal(G.showProductions(g25), 'q0 ⇒ aq1 | bq2, q1 ⇒ aq1 | bq2, q2 ⇒ aq3 | a | bq2, q3 ⇒ aq3 | a | bq1');
  const forms = G.parseDerivation('q0 ⇒ aq1 ⇒ aaq1 ⇒ aabq2 ⇒ aabaq3 ⇒ aabaa', g25);
  assert.ok(G.checkDerivation(forms, g25, 'aabaa').ok);
  assert.deepEqual(M.runDFSA(m25, 'aabaa').path, ['q0', 'q1', 'q1', 'q2', 'q3', 'q3']);
  // student's grammar typed with q-names
  const typed = gr('q0 ⇒ aq1 | bq2\nq1 ⇒ aq1|bq2\nq2 ⇒ aq3|a|bq2\nq3⇒aq3|a|bq1');
  assert.equal(typed.S, 'q0');
  assert.equal(G.classify(typed).type, 'regular');
});

test('2024 Q4 and 2025 Q4 derivations and trees', () => {
  const g = gr('S ⇒ 1S00 | λ');
  const f = G.parseDerivation('S ⇒ 1S00 ⇒ 11S0000 ⇒ 111S000000 ⇒ 111000000', g);
  assert.ok(G.checkDerivation(f, g, '111000000').ok);
  const g2 = gr('S ⇒ ABA, A ⇒ 0A0|0, B ⇒ 1B1|1');
  const f2 = G.parseDerivation('S ⇒ ABA ⇒ 0A0BA ⇒ 000BA ⇒ 0001B1A ⇒ 00011B11A ⇒ 00011111A ⇒ 000111110', g2);
  assert.ok(G.checkDerivation(f2, g2, '000111110').ok);
  const bad = G.parseDerivation('S ⇒ ABA ⇒ 0A0B0', g2);
  const r = G.checkDerivation(bad, g2, '000111110');
  assert.equal(r.ok, false);
  assert.match(r.message, /More than one|not a production/);
  assert.ok(G.findDerivation(g2, '000111110'));
});

test('grammar types (course definitions)', () => {
  assert.equal(G.classify(gr('S ⇒ 0A, 0A ⇒ 00A | 00')).type, 'context-sensitive');
  const cs = gr('S ⇒ A, A ⇒ aABC | abC, CB ⇒ XB, XB ⇒ XY, XY ⇒ BY, BY ⇒ BC, bB ⇒ bb, bC ⇒ bc, cC ⇒ cc');
  assert.equal(G.classify(cs).type, 'context-sensitive');
  assert.deepEqual([...G.language(cs, 9)].sort(), ['aaabbbccc', 'aabbcc', 'abc']);
  const t6 = gr('S ⇒ 0SAB | λ, BA ⇒ AB, 0A ⇒ 01, 1A ⇒ 11, 1B ⇒ 12, 2B ⇒ 22');
  assert.equal(G.classify(t6).type, 'unrestricted');
  const d = G.parseDerivation('S ⇒ 0SAB ⇒ 00SABAB ⇒ 00ABAB ⇒ 00AABB ⇒ 001ABB ⇒ 0011BB ⇒ 00112B ⇒ 001122', t6);
  assert.ok(G.checkDerivation(d, t6, '001122').ok);
  assert.equal(G.classify(gr('S ⇒ A1A, A ⇒ 0A | λ')).type, 'unrestricted');
  assert.equal(G.classify(gr('S ⇒ AB|A|B|λ, A ⇒ 0A|0, B ⇒ 1B|1')).type, 'context-free');
  assert.equal(G.classify(gr('S ⇒ 0A|λ, A ⇒ 0A|1B|1, B ⇒ 1B|1')).type, 'regular');
  const why = G.classify(gr('S ⇒ 0S0|1S1|0|1|λ')).why.regular;
  assert.ok(why.length > 0);
});

test('regular expressions as targets', () => {
  const re = G.regexToJS('a*ba*');
  assert.ok(re.test('aab') && re.test('b') && !re.test('abb'));
  const g = gr('S ⇒ aS | bA | b, A ⇒ aA | a');
  assert.ok(G.checkDesign(g, { alphabet: ['a', 'b'], test: (w) => re.test(w), maxLen: 8, requireType: 'regular' }).ok);
  const r2 = G.checkDesign(gr('S ⇒ AbA, A ⇒ aA | λ'), { alphabet: ['a', 'b'], test: (w) => re.test(w), maxLen: 8, requireType: 'regular' });
  assert.equal(r2.typeFail, true);
  assert.ok(G.regexToJS('0(λ+1+11)0').test('00'));
});

test('random generators produce sensible machines', () => {
  for (let s = 1; s < 40; s++) {
    const rng = new Rng(s);
    const { m } = M.randomDFSA(rng);
    assert.ok(m.edges.length === m.states.length * 2);
    const g = M.randomRegularGrammar(new Rng(s));
    assert.equal(G.classify(g).type, 'regular');
  }
});

test('Turing numbers: 2024, 2025, tutorial 5', () => {
  const d24 = TM.decode('10001 10001 11111 10001 11110 10001 11111 10010 11110 10000 11111 11011', { partial: true });
  assert.deepEqual(d24.errors, []);
  assert.equal(d24.N, 11);
  assert.deepEqual(d24.delta[0], { 0: [1, '1'], 1: [2, '0'], b: null });
  assert.equal(d24.symbols.join(''), '11/1,1/2,0/⊥');
  const d25 = TM.decode('10011 11111 10001 11110 10001 11111 10001 11110 11101 11111 11011 11111', { partial: true });
  assert.equal(d25.N, 3);
  assert.deepEqual(d25.delta[0], { 0: [1, '1'], 1: [1, 'R'], b: null });
  assert.equal(d25.symbols.join(''), '3/1,1/1,R/⊥/');
  const t5a = TM.decode('10001 11111 11011 11111 11011 11111 11011');
  assert.ok(t5a.complete);
  const t5d = TM.decode('10001 11111 11011 11111 11011 11111 10010 11110 11010');
  assert.equal(t5d.complete, false);
  assert.match(t5d.errors[0], /State 2/);
  assert.equal(TM.encode({ N: 0, delta: {} }), '10000');
  // TM3 example prefix
  const ex = { N: 19, delta: { 0: { 0: null, 1: [1, '0'], b: null }, 1: { 0: [2, 'R'], 1: null, b: null }, 2: { 0: null, 1: [3, 'b'], b: [5, 'L'] } } };
  assert.ok(TM.encode(ex).startsWith('1000111001111111101111111100011111010000111111101111111'));
  for (let s = 1; s < 50; s++) {
    const ntm = TM.randomNTM(new Rng(s));
    const back = TM.decode(TM.encode(ntm));
    assert.ok(back.complete, back.errors.join(';'));
    assert.deepEqual(back.N, ntm.N);
  }
});

test('Moore machines (tutorial 5)', () => {
  assert.equal(runMoore(TUT5, '110').out, '100');
  const r = runMoore(TUT5, '11010011');
  assert.equal(r.out, '10010001');
  assert.deepEqual(r.path, ['q0', 'q2', 'q1', 'q1', 'q2', 'q3', 'q3', 'q1', 'q2']);
  const swap = { states: ['q0', 'q1', 'q2'], start: 'q0', delta: { q0: { 1: 'q1', 0: 'q2' }, q1: { 1: 'q1', 0: 'q2' }, q2: { 0: 'q2', 1: 'q1' } }, g: { q1: '0', q2: '1' } };
  assert.ok(checkMooreDesign(swap, MOORE_TARGETS[0]).ok);
  assert.equal(runMoore(swap, '1011').out, '0100');
  assert.equal(checkMooreDesign(swap, MOORE_TARGETS[1]).ok, false);
});
