import test from 'node:test';
import assert from 'node:assert/strict';
import { parsePred, showPred, comparePred, describeWorld, checkPushStep, pushAll, tryParsePred } from '../src/engines/pred.js';
import { SCENARIOS, sentences, SCENARIO_IDS } from '../src/data/predbank.js';

const dogs = SCENARIOS.dogs;
const cmp = (u, r, scen = dogs) => comparePred(parsePred(u), parsePred(r), scen.sig);

test('parse and print like the lecturer', () => {
  assert.equal(showPred(parsePred('∀x ∃y : P(x, y)')), '∀x ∃y : P(x, y)');
  assert.equal(showPred(parsePred('forall x exists y P(x,y)')), '∀x ∃y : P(x, y)');
  assert.equal(showPred(parsePred('¬∃x ∀y : P(x, y)')), '¬∃x ∀y : P(x, y)');
  assert.equal(showPred(parsePred('∃x ¬∃y : P(x, y)')), '∃x ¬∃y : P(x, y)');
  assert.equal(showPred(parsePred('∀x ∈ X ¬∃y ∈ Y : ¬P(x, y)')), '∀x ∈ X ¬∃y ∈ Y : ¬P(x, y)');
  assert.equal(showPred(parsePred('∃x∃y∃z P(x,y) & P(x,z) & y != z')), '∃x ∃y ∃z : P(x, y) ∧ P(x, z) ∧ (y ≠ z)');
  assert.equal(showPred(parsePred('∀x : P(x) → Q(x)')), '∀x : P(x) → Q(x)');
  assert.equal(tryParsePred('∀x P(x').ok, false);
  assert.equal(tryParsePred('∀ P(x)').ok, false);
});

test('2025 Q9 translations are recognised in several equivalent forms', () => {
  assert.ok(cmp('∀x ∈ X ∃y ∈ Y : P(x, y)', '∀x ∃y : P(x, y)').equiv);
  assert.ok(cmp('∀x ∃y : ¬P(x, y)', '¬∃x ∀y : P(x, y)').equiv);
  assert.ok(cmp('∃x ∀y : ¬P(x, y)', '∃x ¬∃y : P(x, y)').equiv);
  assert.ok(cmp('∀x ∀y : P(x, y)', '∀x ¬∃y : ¬P(x, y)').equiv);
  const bad = cmp('∃y ∀x : P(x, y)', '∃x ∀y : P(x, y)');
  assert.equal(bad.equiv, false);
  const txt = describeWorld(bad.world, dogs);
  assert.match(txt, /dog/);
});

test('variables named differently or with swapped letters still type-check', () => {
  assert.ok(cmp('∀a ∃b : P(a, b)', '∀x ∃y : P(x, y)').equiv);
  assert.ok(cmp('∀y ∃x : P(y, x)', '∀x ∃y : P(x, y)').equiv);
  const r = cmp('∀x : P(x, x)', '∀x ∃y : P(x, y)');
  assert.ok(r.error);
});

test('2023 Q8: more than one instrument', () => {
  const m = SCENARIOS.music;
  assert.ok(cmp('∃x∃y∃z P(x,y) ∧ P(x,z) ∧ y ≠ z', '∃x ∃y ∃z : P(x, y) ∧ P(x, z) ∧ (y ≠ z)', m).equiv);
  assert.equal(cmp('∃x∃y∃z P(x,y) ∧ P(x,z)', '∃x ∃y ∃z : P(x, y) ∧ P(x, z) ∧ (y ≠ z)', m).equiv, false);
});

test('friends and crows', () => {
  const f = SCENARIOS.friends;
  assert.ok(cmp('∀y ∃x : P(x, y)', '¬∃y ¬∃x : P(x, y)', f).equiv);
  assert.ok(cmp('∀x ∀y : P(x,y) -> P(y,x)', '∀x ∀y : P(x, y) → P(y, x)', f).equiv);
  const c = SCENARIOS.crows;
  assert.ok(cmp('∀x : P(x) → Q(x)', '¬∃x : P(x) ∧ ¬Q(x)', c).equiv);
  assert.ok(cmp('¬∀x : (P(x) ∨ Q(x))', '∃x : ¬P(x) ∧ ¬Q(x)', c).equiv);
  assert.equal(cmp('∀x : P(x) ∧ Q(x)', '∀x : P(x) → Q(x)', c).equiv, false);
});

test('every bank sentence parses and type-checks', () => {
  for (const id of SCENARIO_IDS) {
    for (const s of sentences(id)) {
      const r = tryParsePred(s.f);
      assert.ok(r.ok, id + ' ' + s.f + ' ' + r.error);
      const c = comparePred(r.ast, r.ast, SCENARIOS[id].sig);
      assert.ok(c.equiv, id + ' ' + s.f + ' ' + c.error);
      assert.ok(s.en, id + ' ' + s.id);
    }
  }
});

test('generalised De Morgan steps', () => {
  const a = parsePred('∃x ¬∃y ∀z : ¬Q(x, y, z)');
  const b = parsePred('∃x ∀y ¬∀z : ¬Q(x, y, z)');
  const c = parsePred('∃x ∀y ∃z : ¬¬Q(x, y, z)');
  const d = parsePred('∃x ∀y ∃z : Q(x, y, z)');
  assert.ok(checkPushStep(a, b).ok);
  assert.ok(checkPushStep(b, c).ok);
  assert.ok(checkPushStep(c, d).ok);
  assert.equal(showPred(pushAll(a)), '∃x ∀y ∃z : Q(x, y, z)');
  assert.equal(checkPushStep(a, parsePred('∀x ∀y ∃z : Q(x, y, z)')).ok, false);
});
