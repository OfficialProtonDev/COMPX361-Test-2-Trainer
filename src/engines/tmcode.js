// Turing numbers of normalised Turing machines (TM3): the code table, encoding and decoding.

export const CODE = {
  0: '10000', 1: '10001', 2: '10010', 3: '10011', 4: '10100', 5: '10101', 6: '10110', 7: '10111', 8: '11000', 9: '11001',
  b: '11010', '⊥': '11011', L: '11100', R: '11101', ',': '11110', '/': '11111',
};
export const DECODE = Object.fromEntries(Object.entries(CODE).map(([k, v]) => [v, k]));
export const TABLE_ORDER = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'b', '⊥', 'L', 'R', ',', '/'];
export const READS = ['0', '1', 'b'];
export const ACTIONS = ['0', '1', 'b', 'L', 'R'];

// ntm = { N, delta: { [state]: { '0': [to, act] | null, '1': …, 'b': … } } }   states 0..N, N = halt
export function symbolsOf(ntm) {
  const out = [...String(ntm.N)];
  for (let q = 0; q < ntm.N; q++) {
    for (const r of READS) {
      out.push('/');
      const tr = ntm.delta[q]?.[r];
      if (!tr) out.push('⊥');
      else out.push(...String(tr[0]), ',', tr[1]);
    }
  }
  return out;
}

export const symbolsText = (syms) => syms.join('').replace(/,/g, ', ').replace(/\//g, '/');
export const bitsOf = (syms) => syms.map((s) => CODE[s]).join('');
export const blocksOf = (bits) => bits.match(/.{1,5}/g) || [];
export function encode(ntm) { return bitsOf(symbolsOf(ntm)); }

// Decode bits. With partial = true the string is only the first part of a Turing number.
export function decode(bits, { partial = false } = {}) {
  const clean = bits.replace(/\s+/g, '');
  const res = { blocks: [], symbols: [], errors: [], N: null, delta: {}, instructions: [], complete: false };
  if (!/^[01]*$/.test(clean)) { res.errors.push('Only 0s and 1s are allowed.'); return res; }
  if (!partial && clean.length % 5) res.errors.push(`The length (${clean.length} bits) isn't a multiple of 5, so it can't be split into codes.`);
  res.blocks = blocksOf(clean);
  for (const b of res.blocks) {
    if (b.length < 5) { if (!partial) res.errors.push(`The last block “${b}” is incomplete.`); break; }
    const s = DECODE[b];
    if (s === undefined) { res.errors.push(`“${b}” isn't a code in the table (every code starts with 1).`); res.symbols.push('?'); }
    else res.symbols.push(s);
  }
  if (res.errors.length) return res;
  // split on '/'
  const parts = []; let cur = [];
  for (const s of res.symbols) { if (s === '/') { parts.push(cur); cur = []; } else cur.push(s); }
  parts.push(cur);
  const head = parts[0];
  if (!head.length || head.some((s) => !/[0-9]/.test(s))) { res.errors.push('A Turing number must start with the halt state N (digits), then “/”.'); return res; }
  if (head.length > 1 && head[0] === '0') { res.errors.push('The halt state has a leading zero.'); return res; }
  res.N = Number(head.join(''));
  const instr = parts.slice(1);
  const expected = 3 * res.N;
  const lastIncomplete = partial && res.symbols[res.symbols.length - 1] !== '/' ;
  instr.forEach((p, idx) => {
    const q = Math.floor(idx / 3), r = READS[idx % 3];
    const isLast = idx === instr.length - 1;
    const rec = { idx, state: q, read: r, text: p.join('').replace(',', ', '), raw: p };
    if (q >= res.N) { rec.error = res.N === 1 ? 'There is only 1 non-halt state (state 0), so this instruction is one too many.' : `There are only ${res.N} non-halt states (0 to ${res.N - 1}), so this instruction is one too many.`; res.errors.push(rec.error); res.instructions.push(rec); return; }
    if (!p.length) {
      if (partial && isLast) { rec.unknown = true; res.instructions.push(rec); return; }
      rec.error = 'Empty instruction between two “/”.'; res.errors.push(rec.error); res.instructions.push(rec); return;
    }
    if (p.length === 1 && p[0] === '⊥') { rec.undefined = true; (res.delta[q] ||= {})[r] = null; res.instructions.push(rec); return; }
    const comma = p.indexOf(',');
    const digits = comma === -1 ? p : p.slice(0, comma);
    if (partial && isLast && lastIncomplete && (comma === -1 || comma === p.length - 1)) { rec.unknown = true; rec.partialText = p.join(''); res.instructions.push(rec); return; }
    if (comma === -1 || comma === p.length - 1 || p.length - comma !== 2 || !digits.length || digits.some((s) => !/[0-9]/.test(s))) {
      rec.error = `“${p.join('')}” should be ⊥ or “state, action” (for example 2, R).`; res.errors.push(rec.error); res.instructions.push(rec); return;
    }
    const to = Number(digits.join(''));
    const act = p[comma + 1];
    if (!ACTIONS.includes(act)) { rec.error = `“${act}” isn't an action: write 0, 1 or b, or move L or R.`; res.errors.push(rec.error); res.instructions.push(rec); return; }
    if (to > res.N) { rec.error = `State ${to} is referenced, but the halt state is ${res.N}, so the states are 0 to ${res.N}.`; res.errors.push(rec.error); res.instructions.push(rec); return; }
    rec.to = to; rec.act = act;
    (res.delta[q] ||= {})[r] = [to, act];
    res.instructions.push(rec);
  });
  if (!partial && !res.errors.length && instr.length !== expected) {
    res.errors.push(`With halt state ${res.N} there must be exactly ${expected} instructions (3 for each of states 0 to ${res.N - 1}), but there are ${instr.length}.`);
  }
  res.complete = !partial && !res.errors.length;
  return res;
}

export function edgesOf(delta) {
  const edges = [];
  for (const [q, row] of Object.entries(delta)) {
    for (const r of READS) {
      const tr = row[r];
      if (!tr) continue;
      let e = edges.find((x) => x.from === Number(q) && x.to === tr[0]);
      if (!e) edges.push((e = { from: Number(q), to: tr[0], labels: [] }));
      e.labels.push(`${r}/${tr[1]}`);
    }
  }
  return edges;
}

export function randomNTM(rng, { N = rng.pick([2, 3, 3, 4, 5, 11, 12]), fill = 0.6 } = {}) {
  const delta = {};
  const small = Math.min(N, 4);
  for (let q = 0; q < N; q++) {
    delta[q] = {};
    for (const r of READS) {
      if (rng.chance(fill) || (q === 0 && r !== 'b' && Object.keys(delta[0]).length === 0)) {
        const to = rng.chance(0.25) ? N : rng.int(0, Math.min(N - 1, small));
        delta[q][r] = [to, rng.pick(ACTIONS)];
      } else delta[q][r] = null;
    }
  }
  return { N, delta };
}

// First sixty bits (12 codes) of a Turing number, as in the 2024 and 2025 tests.
export function first60(ntm) { return encode(ntm).slice(0, 60); }

export function spaced(bits) { return blocksOf(bits).join(' '); }
