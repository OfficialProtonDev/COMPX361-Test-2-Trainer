import test from 'node:test';
import assert from 'node:assert/strict';
import { parse, same, equivalent, consequence, status } from '../src/engines/prop.js';
import { checkStep } from '../src/engines/laws.js';
import { LAW_BANK, EQUIV_BANK, NAND_BANK, STATUS_BANK, DNF_SPECIAL } from '../src/data/propbank.js';
import { convert, checkRestricted, solutionSteps } from '../src/engines/nand.js';

test('every worked law path is valid line by line', () => {
  for (const ex of LAW_BANK) {
    let prev = parse(ex.a);
    for (const [f, laws] of ex.path) {
      const next = parse(f);
      const r = checkStep(prev, next, laws);
      assert.ok(r.ok, `${ex.id}: ${f} by ${laws}: ${r.message}`);
      prev = next;
    }
    assert.ok(same(prev, parse(ex.b)), `${ex.id} ends at goal`);
  }
});

test('equivalence bank relations are right', () => {
  for (const e of EQUIV_BANK) {
    const a = parse(e.a), b = parse(e.b);
    const eq = equivalent(a, b).equiv, ab = consequence(a, b).holds, ba = consequence(b, a).holds;
    const rel = eq ? 'equiv' : ab ? 'conseq' : ba ? 'reverse' : 'neither';
    assert.equal(rel, e.rel, `${e.a} vs ${e.b}`);
  }
});

test('restricted connective conversions', () => {
  for (const e of NAND_BANK) {
    const f = parse(e.f);
    const out = convert(f, e.target);
    const r = checkRestricted(out, f, e.target);
    assert.ok(r.ok, `${e.f} → ${e.target}: ${JSON.stringify(r)}`);
    const steps = solutionSteps(f, e.target);
    const last = steps[steps.length - 1].f;
    assert.ok(checkRestricted(last, f, e.target).ok, `${e.f} steps end in target`);
    for (const s of steps) assert.ok(equivalent(s.f, f).equiv);
  }
  for (const s of STATUS_BANK) assert.ok(status(parse(s.f)).label);
  for (const d of DNF_SPECIAL) assert.ok(parse(d.f));
});

import * as G from '../src/engines/gram.js';
import { CFG_BANK, CS_BANK, DESIGN, CLASSIFY_POOL } from '../src/data/grambank.js';

test('grammar banks: every target derivable, every model grammar correct', () => {
  for (const b of [...CFG_BANK, ...CS_BANK]) {
    const r = G.parseGrammar(b.text);
    assert.ok(r.ok, b.id + r.errors);
    for (const t of b.targets) {
      const d = G.findDerivation(r.g, t, 200000);
      assert.ok(d, `${b.id}: no derivation for ${t}`);
    }
  }
  for (const d of DESIGN) {
    const r = G.parseGrammar(d.model);
    assert.ok(r.ok, d.id);
    const c = G.checkDesign(r.g, { alphabet: d.alphabet, test: d.test, maxLen: d.maxLen, requireType: d.req });
    assert.ok(c.ok, `${d.id}: ${c.message}`);
  }
  for (const c of CLASSIFY_POOL) assert.ok(G.parseGrammar(c.text).ok, c.text);
  // 2023 regular grammar language description
  const g23 = G.parseGrammar(CFG_BANK.find((x) => x.id === 't23q2').text).g;
  const L = G.language(g23, 6);
  for (const w of G.allStrings(['0', '1'], 6)) {
    const want = w === '' || (w.length >= 2 && w[w.length - 1] !== w[w.length - 2]);
    assert.equal(L.has(w), want, 't23q2 ' + w);
  }
});
