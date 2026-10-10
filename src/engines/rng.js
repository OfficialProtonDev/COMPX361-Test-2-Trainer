// Seeded random numbers so every generated question can be reproduced from its seed.
export function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a |= 0; a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

export class Rng {
  constructor(seed) {
    this.seed = (seed >>> 0) || 1;
    this.f = mulberry32(this.seed);
  }
  next() { return this.f(); }
  int(lo, hi) { return lo + Math.floor(this.f() * (hi - lo + 1)); }
  pick(arr) { return arr[Math.floor(this.f() * arr.length)]; }
  chance(p) { return this.f() < p; }
  shuffle(arr) {
    const a = arr.slice();
    for (let i = a.length - 1; i > 0; i--) {
      const j = Math.floor(this.f() * (i + 1));
      [a[i], a[j]] = [a[j], a[i]];
    }
    return a;
  }
  sample(arr, k) { return this.shuffle(arr).slice(0, k); }
  weighted(items) { // items: [[value, weight], ...]
    const total = items.reduce((s, [, w]) => s + w, 0);
    let r = this.f() * total;
    for (const [v, w] of items) { if ((r -= w) < 0) return v; }
    return items[items.length - 1][0];
  }
}

export function newSeed() {
  return (Math.floor(Math.random() * 0x7fffffff) ^ (Date.now() & 0xffff)) >>> 0 || 7;
}
