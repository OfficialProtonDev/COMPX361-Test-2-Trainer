import test from 'node:test';
import assert from 'node:assert/strict';
import { BANK, generated, checkChain, checkBase, checkStatement, modelProof, stampBases, checkStampRep } from '../src/engines/induction.js';

const chainOf = (p) => [{ e: p.lhs1 }, ...p.chain.map((c) => ({ rel: c.rel, e: c.e, why: c.why }))];

test('every canonical chain checks out', () => {
  for (const p of BANK) {
    if (p.kind === 'stamps') continue;
    const r = checkChain(p, chainOf(p));
    const bad = r.results.findIndex((x) => !x.ok);
    assert.ok(r.ok && bad === -1, `${p.id}: line ${bad}: ${r.results[bad]?.message}`);
    assert.ok(r.overall.ok, `${p.id}: ${r.overall.message}`);
  }
});

test('generated problems check out', () => {
  for (const kind of ['div', 'recur']) {
    for (let seed = 1; seed < 60; seed++) {
      const p = generated(kind, seed);
      const r = checkChain(p, chainOf(p));
      const bad = r.results.findIndex((x) => !x.ok);
      assert.ok(r.ok && bad === -1, `${p.id}: line ${bad}: ${r.results[bad]?.message} :: ${chainOf(p)[bad]?.e}`);
      assert.ok(r.overall.ok, `${p.id}: ${r.overall.message}`);
      for (const b of p.base || []) if (p.kind !== 'div') assert.ok(checkBase(p, b.n, b.inst).ok, `${p.id} base ${b.n}`);
    }
  }
  for (let seed = 1; seed < 30; seed++) {
    const p = generated('stamps', seed);
    for (const r of stampBases(p)) assert.ok(checkStampRep(p, r.n, r.x, r.y).ok, `${p.id} ${r.n}`);
  }
});

test('base cases accept instance or simplified forms', () => {
  for (const p of BANK) {
    if (['div', 'parity', 'stamps'].includes(p.kind)) continue;
    for (const b of p.base) {
      assert.ok(checkBase(p, b.n, b.inst).ok, `${p.id} inst ${b.inst}: ${checkBase(p, b.n, b.inst).message}`);
    }
  }
  const sq = BANK.find((p) => p.id === 'ineq-sq');
  assert.equal(checkBase(sq, 3, '3^2 >= 2*3').ok, false);
  assert.equal(checkBase(sq, 3, '9 >= 7').ok, true);
});

test('statements in n, k and k + 1', () => {
  const s = BANK.find((p) => p.id === 'sum-ii1');
  assert.ok(checkStatement(s, '1·2 + 2·3 + ... + n(n+1) = n(n+1)(n+2)/3', 'n').ok);
  assert.ok(checkStatement(s, 'S(k+1) = (k+1)(k+2)(k+3)/3', 'k+1').ok);
  assert.ok(checkStatement(s, '1*2 + 2*3 + ... + (k+1)(k+2) = (k+1)(k+2)(k+3)/3', 'k+1').ok);
  assert.equal(checkStatement(s, '1*2 + 2*3 + ... + (k+1)(k+2) = (k+1)(k+2)(k+2)/3', 'k+1').ok, false);
  assert.equal(checkStatement(s, 'S(k) + 1 = (k+1)(k+2)(k+3)/3', 'k+1').ok, false);
  const q = BANK.find((p) => p.id === 'ineq-2025');
  assert.ok(checkStatement(q, 'n^2 + 2n - 7 > 0', 'n').ok);
  assert.ok(checkStatement(q, 'n^2 + 2n > 7', 'n').ok);
  assert.ok(checkStatement(q, '(k+1)^2 + 2(k+1) - 7 > 0', 'k+1').ok);
  assert.equal(checkStatement(q, 'k^2 + 2k - 7 > 0', 'k+1').ok, false);
  assert.equal(checkStatement(q, 'n^2 + 2n - 7 >= 0', 'n').ok, false);
  const r = BANK.find((p) => p.id === 'strong-2024');
  assert.ok(checkStatement(r, 'a_k >= 2^k', 'k').ok);
  assert.ok(checkStatement(r, 'a_{k+1} >= 2^(k+1)', 'k+1').ok);
});

test('chain catches common mistakes', () => {
  const p = BANK.find((x) => x.id === 'ineq-sq');
  // bad algebra
  let r = checkChain(p, [{ e: '(k+1)^2' }, { rel: '=', e: 'k^2 + k + 1', why: 'alg' }]);
  assert.equal(r.ok, false); assert.match(r.results[1].message, /false/);
  // wrong start
  r = checkChain(p, [{ e: 'k^2 + 1' }]);
  assert.match(r.results[0].message, /left-hand side/);
  // no IH marked
  r = checkChain(p, [{ e: '(k+1)^2' }, { rel: '=', e: 'k^2+2k+1', why: 'alg' }, { rel: '≥', e: '(2k+1)+2k+1', why: 'alg' }, { rel: '≥', e: '2(k+1)+1', why: 'alg' }]);
  assert.match(r.overall.message, /hypothesis/);
  // relation reversed
  r = checkChain(p, [{ e: '(k+1)^2' }, { rel: '≤', e: 'k^2+2k+1', why: 'alg' }, { rel: '≤', e: '(2k+1)+2k+1', why: 'ih' }]);
  assert.equal(r.ok, false);
  const d = BANK.find((x) => x.id === 'div-5');
  r = checkChain(d, [{ e: '5^(k+1) - 1' }, { rel: '=', e: '5*5^k - 1', why: 'alg' }, { rel: '=', e: '5(4q+1) - 1', why: 'ih' }, { rel: '=', e: '20q + 4', why: 'alg' }]);
  assert.equal(r.overall.ok, false);
  assert.match(r.overall.message, /4 ×/);
});

test('model proofs render', () => {
  for (const p of BANK) {
    const m = modelProof(p);
    assert.ok(m.length >= 4, p.id);
    assert.ok(m.join('\n').includes('□'), p.id);
  }
  const p = generated('recur', 3);
  assert.ok(modelProof(p).join('\n').includes('strong induction'));
});
