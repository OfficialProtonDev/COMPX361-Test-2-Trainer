// Induction problems (IND1–IND3, tutorial 9, past tests) and the checks behind the proof builder.
import * as A from './algebra.js';
import { Rng } from './rng.js';

const Qi = (x) => A.Q(BigInt(x));

export const REASONS = {
  alg: 'algebra',
  split: 'split off the last term',
  rec: 'by the recurrence',
  ih: 'by P(k)',
  ihs: 'by P(k) and P(k−1)',
  since: 'since k is large enough',
  part: 'by part (a)',
};

// ---------------------------------------------------------------- the bank
// Expression strings use the algebra parser: S(x) is the question's sum, a(x) or a_{x} its sequence,
// q is the integer from the hypothesis in divisibility proofs.
const B = [];
const add = (p) => B.push(p);

// ---- sums
add({ id: 'sum-sq', src: 'IND1 lecture example', title: 'Sum of squares', kind: 'eq', n0: 1,
  ask: 'Show that for all n ≥ 1,  1² + 2² + ⋯ + n² = n(n + 1)(2n + 1)/6.',
  sum: { term: 'i^2', from: 1 }, lhs: 'S(n)', rel: '=', rhs: 'n(n+1)(2n+1)/6',
  P: { n: '1² + 2² + ⋯ + n² = n(n + 1)(2n + 1)/6', k: '1² + 2² + ⋯ + k² = k(k + 1)(2k + 1)/6', k1: '1² + 2² + ⋯ + (k + 1)² = (k + 1)(k + 2)(2k + 3)/6' },
  base: [{ n: 1, inst: '1² = 1 × 2 × 3/6', simp: '1 = 1' }],
  lhs1: 'S(k+1)', lhsShow: '1² + 2² + ⋯ + (k + 1)²', chain: [
    { rel: '=', e: 'S(k) + (k+1)^2', why: 'split', show: '(1² + 2² + ⋯ + k²) + (k + 1)²' },
    { rel: '=', e: 'k(k+1)(2k+1)/6 + (k+1)^2', why: 'ih' },
    { rel: '=', e: '(k(k+1)(2k+1) + 6(k+1)^2)/6', why: 'alg' },
    { rel: '=', e: '(k+1)(k(2k+1) + 6(k+1))/6', why: 'alg' },
    { rel: '=', e: '(k+1)(2k^2 + 7k + 6)/6', why: 'alg' },
    { rel: '=', e: '(k+1)(k+2)(2k+3)/6', why: 'alg' }] });

add({ id: 'sum-ii1', src: 'Tutorial 9 Q1(a)', title: 'Sum of n(n + 1)', kind: 'eq', n0: 1,
  ask: 'Prove by induction that 1·2 + 2·3 + ⋯ + n(n + 1) = n(n + 1)(n + 2)/3 for all n ≥ 1.',
  sum: { term: 'i(i+1)', from: 1 }, lhs: 'S(n)', rel: '=', rhs: 'n(n+1)(n+2)/3',
  P: { n: '1·2 + 2·3 + ⋯ + n(n + 1) = n(n + 1)(n + 2)/3', k: '1·2 + 2·3 + ⋯ + k(k + 1) = k(k + 1)(k + 2)/3', k1: '1·2 + 2·3 + ⋯ + (k + 1)(k + 2) = (k + 1)(k + 2)(k + 3)/3' },
  base: [{ n: 1, inst: '1 × 2 = 1 × 2 × 3/3', simp: '2 = 2' }],
  lhs1: 'S(k+1)', lhsShow: '1·2 + 2·3 + ⋯ + (k + 1)(k + 2)', chain: [
    { rel: '=', e: 'S(k) + (k+1)(k+2)', why: 'split', show: '[1·2 + 2·3 + ⋯ + k(k + 1)] + (k + 1)(k + 2)' },
    { rel: '=', e: 'k(k+1)(k+2)/3 + (k+1)(k+2)', why: 'ih' },
    { rel: '=', e: '(k(k+1)(k+2) + 3(k+1)(k+2))/3', why: 'alg' },
    { rel: '=', e: '(k+1)(k+2)(k+3)/3', why: 'alg' }] });

add({ id: 'sum-i', src: 'classic', title: 'Sum of the first n numbers', kind: 'eq', n0: 1,
  ask: 'Prove by induction that 1 + 2 + ⋯ + n = n(n + 1)/2 for all n ≥ 1.',
  sum: { term: 'i', from: 1 }, lhs: 'S(n)', rel: '=', rhs: 'n(n+1)/2',
  P: { n: '1 + 2 + ⋯ + n = n(n + 1)/2', k: '1 + 2 + ⋯ + k = k(k + 1)/2', k1: '1 + 2 + ⋯ + (k + 1) = (k + 1)(k + 2)/2' },
  base: [{ n: 1, inst: '1 = 1 × 2/2', simp: '1 = 1' }],
  lhs1: 'S(k+1)', lhsShow: '1 + 2 + ⋯ + (k + 1)', chain: [
    { rel: '=', e: 'S(k) + (k+1)', why: 'split', show: '(1 + 2 + ⋯ + k) + (k + 1)' },
    { rel: '=', e: 'k(k+1)/2 + (k+1)', why: 'ih' },
    { rel: '=', e: '(k(k+1) + 2(k+1))/2', why: 'alg' },
    { rel: '=', e: '(k+1)(k+2)/2', why: 'alg' }] });

add({ id: 'sum-odd', src: 'classic', title: 'Sum of odd numbers', kind: 'eq', n0: 1,
  ask: 'Prove by induction that 1 + 3 + 5 + ⋯ + (2n − 1) = n² for all n ≥ 1.',
  sum: { term: '2i-1', from: 1 }, lhs: 'S(n)', rel: '=', rhs: 'n^2',
  P: { n: '1 + 3 + ⋯ + (2n − 1) = n²', k: '1 + 3 + ⋯ + (2k − 1) = k²', k1: '1 + 3 + ⋯ + (2k + 1) = (k + 1)²' },
  base: [{ n: 1, inst: '1 = 1²', simp: '1 = 1' }],
  lhs1: 'S(k+1)', lhsShow: '1 + 3 + ⋯ + (2k + 1)', chain: [
    { rel: '=', e: 'S(k) + (2k+1)', why: 'split', show: '[1 + 3 + ⋯ + (2k − 1)] + (2k + 1)' },
    { rel: '=', e: 'k^2 + 2k + 1', why: 'ih' },
    { rel: '=', e: '(k+1)^2', why: 'alg' }] });

add({ id: 'sum-cube', src: 'classic', title: 'Sum of cubes', kind: 'eq', n0: 1,
  ask: 'Prove by induction that 1³ + 2³ + ⋯ + n³ = n²(n + 1)²/4 for all n ≥ 1.',
  sum: { term: 'i^3', from: 1 }, lhs: 'S(n)', rel: '=', rhs: 'n^2(n+1)^2/4',
  P: { n: '1³ + 2³ + ⋯ + n³ = n²(n + 1)²/4', k: '1³ + 2³ + ⋯ + k³ = k²(k + 1)²/4', k1: '1³ + 2³ + ⋯ + (k + 1)³ = (k + 1)²(k + 2)²/4' },
  base: [{ n: 1, inst: '1³ = 1² × 2²/4', simp: '1 = 1' }],
  lhs1: 'S(k+1)', lhsShow: '1³ + 2³ + ⋯ + (k + 1)³', chain: [
    { rel: '=', e: 'S(k) + (k+1)^3', why: 'split', show: '(1³ + 2³ + ⋯ + k³) + (k + 1)³' },
    { rel: '=', e: 'k^2(k+1)^2/4 + (k+1)^3', why: 'ih' },
    { rel: '=', e: '(k+1)^2(k^2 + 4(k+1))/4', why: 'alg' },
    { rel: '=', e: '(k+1)^2(k+2)^2/4', why: 'alg' }] });

add({ id: 'sum-geo', src: 'classic', title: 'Powers of 2', kind: 'eq', n0: 1,
  ask: 'Prove by induction that 1 + 2 + 4 + ⋯ + 2ⁿ⁻¹ = 2ⁿ − 1 for all n ≥ 1.',
  sum: { term: '2^(i-1)', from: 1 }, lhs: 'S(n)', rel: '=', rhs: '2^n - 1',
  P: { n: '1 + 2 + ⋯ + 2ⁿ⁻¹ = 2ⁿ − 1', k: '1 + 2 + ⋯ + 2ᵏ⁻¹ = 2ᵏ − 1', k1: '1 + 2 + ⋯ + 2ᵏ = 2ᵏ⁺¹ − 1' },
  base: [{ n: 1, inst: '1 = 2^1 − 1', simp: '1 = 1' }],
  lhs1: 'S(k+1)', lhsShow: '1 + 2 + ⋯ + 2ᵏ', chain: [
    { rel: '=', e: 'S(k) + 2^k', why: 'split', show: '(1 + 2 + ⋯ + 2ᵏ⁻¹) + 2ᵏ' },
    { rel: '=', e: '2^k - 1 + 2^k', why: 'ih' },
    { rel: '=', e: '2 × 2^k - 1', why: 'alg' },
    { rel: '=', e: '2^(k+1) - 1', why: 'alg' }] });

add({ id: 'sum-tele', src: 'classic', title: 'Telescoping fractions', kind: 'eq', n0: 1,
  ask: 'Prove by induction that 1/(1·2) + 1/(2·3) + ⋯ + 1/(n(n + 1)) = n/(n + 1) for all n ≥ 1.',
  sum: { term: '1/(i(i+1))', from: 1 }, lhs: 'S(n)', rel: '=', rhs: 'n/(n+1)',
  P: { n: '1/(1·2) + ⋯ + 1/(n(n + 1)) = n/(n + 1)', k: '1/(1·2) + ⋯ + 1/(k(k + 1)) = k/(k + 1)', k1: '1/(1·2) + ⋯ + 1/((k + 1)(k + 2)) = (k + 1)/(k + 2)' },
  base: [{ n: 1, inst: '1/(1×2) = 1/2', simp: '1/2 = 1/2' }],
  lhs1: 'S(k+1)', lhsShow: '1/(1·2) + ⋯ + 1/((k + 1)(k + 2))', chain: [
    { rel: '=', e: 'S(k) + 1/((k+1)(k+2))', why: 'split', show: '[1/(1·2) + ⋯ + 1/(k(k + 1))] + 1/((k + 1)(k + 2))' },
    { rel: '=', e: 'k/(k+1) + 1/((k+1)(k+2))', why: 'ih' },
    { rel: '=', e: '(k(k+2) + 1)/((k+1)(k+2))', why: 'alg' },
    { rel: '=', e: '(k+1)^2/((k+1)(k+2))', why: 'alg' },
    { rel: '=', e: '(k+1)/(k+2)', why: 'alg' }] });

add({ id: 'sum-geo3', src: 'classic', title: 'Powers of 3 from n = 0', kind: 'eq', n0: 0,
  ask: 'Prove by induction that 1 + 3 + 3² + ⋯ + 3ⁿ = (3ⁿ⁺¹ − 1)/2 for all n ≥ 0.',
  sum: { term: '3^i', from: 0 }, lhs: 'S(n)', rel: '=', rhs: '(3^(n+1) - 1)/2',
  P: { n: '1 + 3 + ⋯ + 3ⁿ = (3ⁿ⁺¹ − 1)/2', k: '1 + 3 + ⋯ + 3ᵏ = (3ᵏ⁺¹ − 1)/2', k1: '1 + 3 + ⋯ + 3ᵏ⁺¹ = (3ᵏ⁺² − 1)/2' },
  base: [{ n: 0, inst: '3^0 = (3^1 − 1)/2', simp: '1 = 1' }],
  lhs1: 'S(k+1)', lhsShow: '1 + 3 + ⋯ + 3ᵏ⁺¹', chain: [
    { rel: '=', e: 'S(k) + 3^(k+1)', why: 'split', show: '(1 + 3 + ⋯ + 3ᵏ) + 3ᵏ⁺¹' },
    { rel: '=', e: '(3^(k+1) - 1)/2 + 3^(k+1)', why: 'ih' },
    { rel: '=', e: '(3 × 3^(k+1) - 1)/2', why: 'alg' },
    { rel: '=', e: '(3^(k+2) - 1)/2', why: 'alg' }] });

// ---- inequalities
add({ id: 'ineq-2n', src: 'IND1 lecture example', title: '2ⁿ ≥ n + 1', kind: 'ineq', n0: 1,
  ask: 'Prove that for all n ∈ ℕ, 2ⁿ ≥ n + 1.',
  lhs: '2^n', rel: '≥', rhs: 'n+1',
  P: { n: '2ⁿ ≥ n + 1', k: '2ᵏ ≥ k + 1', k1: '2ᵏ⁺¹ ≥ (k + 1) + 1 = k + 2' },
  base: [{ n: 1, inst: '2^1 ≥ 1 + 1', simp: '2 ≥ 2' }],
  lhs1: '2^(k+1)', chain: [
    { rel: '=', e: '2 × 2^k', why: 'alg' },
    { rel: '≥', e: '2(k+1)', why: 'ih' },
    { rel: '=', e: '2k + 2', why: 'alg' },
    { rel: '≥', e: 'k + 2', why: 'since', note: 'since k > 0' }] });

add({ id: 'ineq-sq', src: '2023 Test 2 Q9(a)', title: 'n² ≥ 2n + 1', kind: 'ineq', n0: 3,
  ask: 'Prove by mathematical induction that for all natural numbers n ≥ 3, n² ≥ 2n + 1.',
  lhs: 'n^2', rel: '≥', rhs: '2n+1',
  P: { n: 'n² ≥ 2n + 1', k: 'k² ≥ 2k + 1', k1: '(k + 1)² ≥ 2(k + 1) + 1' },
  base: [{ n: 3, inst: '3² ≥ 2 × 3 + 1', simp: '9 ≥ 7' }],
  lhs1: '(k+1)^2', chain: [
    { rel: '=', e: 'k^2 + 2k + 1', why: 'alg' },
    { rel: '≥', e: '(2k+1) + 2k + 1', why: 'ih' },
    { rel: '=', e: '4k + 2', why: 'alg' },
    { rel: '=', e: '2k + 2k + 2', why: 'alg' },
    { rel: '≥', e: '2k + 2 + 1', why: 'since', note: 'since k ≥ 3' },
    { rel: '=', e: '2(k+1) + 1', why: 'alg' }] });

add({ id: 'ineq-2sq', src: '2023 Test 2 Q9(b)', title: '2ⁿ ≥ n² (using part a)', kind: 'ineq', n0: 4,
  ask: 'Using (a) n² ≥ 2n + 1 for n ≥ 3, prove that for all natural numbers n ≥ 4, 2ⁿ ≥ n².',
  lhs: '2^n', rel: '≥', rhs: 'n^2',
  P: { n: '2ⁿ ≥ n²', k: '2ᵏ ≥ k²', k1: '2ᵏ⁺¹ ≥ (k + 1)²' },
  base: [{ n: 4, inst: '2^4 ≥ 4^2', simp: '16 ≥ 16' }],
  lhs1: '2^(k+1)', chain: [
    { rel: '=', e: '2 × 2^k', why: 'alg' },
    { rel: '≥', e: '2k^2', why: 'ih' },
    { rel: '=', e: 'k^2 + k^2', why: 'alg' },
    { rel: '≥', e: 'k^2 + 2k + 1', why: 'part', note: 'by (a), since k ≥ 4' },
    { rel: '=', e: '(k+1)^2', why: 'alg' }] });

add({ id: 'ineq-quad', src: 'Tutorial 9 Q1(b)', title: 'n² − 7n + 12 ≥ 0', kind: 'ineq', n0: 3,
  ask: 'Prove by induction that n² − 7n + 12 ≥ 0 for all n ≥ 3.',
  lhs: 'n^2 - 7n + 12', rel: '≥', rhs: '0',
  P: { n: 'n² − 7n + 12 ≥ 0', k: 'k² − 7k + 12 ≥ 0', k1: '(k + 1)² − 7(k + 1) + 12 ≥ 0' },
  base: [{ n: 3, inst: '3^2 − 7 × 3 + 12 ≥ 0', simp: '0 ≥ 0' }],
  lhs1: '(k+1)^2 - 7(k+1) + 12', chain: [
    { rel: '=', e: 'k^2 + 2k + 1 - 7k - 7 + 12', why: 'alg' },
    { rel: '=', e: 'k^2 - 5k + 6', why: 'alg' },
    { rel: '=', e: '(k^2 - 7k + 12) + 2(k - 3)', why: 'alg' },
    { rel: '≥', e: '0', why: 'ih', note: 'by P(k) and since k ≥ 3' }] });

add({ id: 'ineq-2025', src: '2025 Test 2 Q10', title: 'n² + 2n − 7 > 0', kind: 'ineq', n0: 2,
  ask: 'Prove by mathematical induction that for all natural numbers n > 1, n² + 2n − 7 > 0.',
  lhs: 'n^2 + 2n - 7', rel: '>', rhs: '0',
  P: { n: 'n² + 2n − 7 > 0', k: 'k² + 2k − 7 > 0', k1: '(k + 1)² + 2(k + 1) − 7 > 0' },
  base: [{ n: 2, inst: '2^2 + 4 − 7 > 0', simp: '1 > 0' }],
  lhs1: '(k+1)^2 + 2(k+1) - 7', chain: [
    { rel: '=', e: 'k^2 + 2k + 1 + 2k + 2 - 7', why: 'alg' },
    { rel: '=', e: '(k^2 + 2k - 7) + 2k + 3', why: 'alg' },
    { rel: '>', e: '0', why: 'ih', note: 'by P(k) and because 2k + 3 > 0 since k > 0' }] });

add({ id: 'ineq-3n', src: 'practice', title: '3ⁿ ≥ 2n + 1', kind: 'ineq', n0: 1,
  ask: 'Prove by induction that 3ⁿ ≥ 2n + 1 for all n ≥ 1.',
  lhs: '3^n', rel: '≥', rhs: '2n+1',
  P: { n: '3ⁿ ≥ 2n + 1', k: '3ᵏ ≥ 2k + 1', k1: '3ᵏ⁺¹ ≥ 2(k + 1) + 1' },
  base: [{ n: 1, inst: '3^1 ≥ 2 × 1 + 1', simp: '3 ≥ 3' }],
  lhs1: '3^(k+1)', chain: [
    { rel: '=', e: '3 × 3^k', why: 'alg' },
    { rel: '≥', e: '3(2k+1)', why: 'ih' },
    { rel: '=', e: '6k + 3', why: 'alg' },
    { rel: '≥', e: '2k + 3', why: 'since', note: 'since k > 0' },
    { rel: '=', e: '2(k+1) + 1', why: 'alg' }] });

add({ id: 'ineq-2n2', src: 'practice', title: '2ⁿ > 2n', kind: 'ineq', n0: 3,
  ask: 'Prove by induction that 2ⁿ > 2n for all n ≥ 3.',
  lhs: '2^n', rel: '>', rhs: '2n',
  P: { n: '2ⁿ > 2n', k: '2ᵏ > 2k', k1: '2ᵏ⁺¹ > 2(k + 1)' },
  base: [{ n: 3, inst: '2^3 > 2 × 3', simp: '8 > 6' }],
  lhs1: '2^(k+1)', chain: [
    { rel: '=', e: '2 × 2^k', why: 'alg' },
    { rel: '>', e: '2 × 2k', why: 'ih' },
    { rel: '=', e: '2k + 2k', why: 'alg' },
    { rel: '≥', e: '2k + 2', why: 'since', note: 'since k ≥ 1' },
    { rel: '=', e: '2(k+1)', why: 'alg' }] });

add({ id: 'ineq-sq6', src: 'practice', title: 'n² ≥ n + 6', kind: 'ineq', n0: 3,
  ask: 'Prove by induction that n² ≥ n + 6 for all n ≥ 3.',
  lhs: 'n^2', rel: '≥', rhs: 'n+6',
  P: { n: 'n² ≥ n + 6', k: 'k² ≥ k + 6', k1: '(k + 1)² ≥ (k + 1) + 6' },
  base: [{ n: 3, inst: '3^2 ≥ 3 + 6', simp: '9 ≥ 9' }],
  lhs1: '(k+1)^2', chain: [
    { rel: '=', e: 'k^2 + 2k + 1', why: 'alg' },
    { rel: '≥', e: '(k + 6) + 2k + 1', why: 'ih' },
    { rel: '=', e: '3k + 7', why: 'alg' },
    { rel: '≥', e: 'k + 7', why: 'since', note: 'since k > 0' },
    { rel: '=', e: '(k+1) + 6', why: 'alg' }] });

// ---- divisibility
add({ id: 'div-5', src: 'IND1 lecture example', title: '5ⁿ − 1 divisible by 4', kind: 'div', n0: 0,
  ask: 'Prove that 5ⁿ − 1 is divisible by 4 for all n ≥ 0.',
  div: { expr: '5^n - 1', d: 4, solveFor: '5^k = 4q + 1' },
  P: { n: '5ⁿ − 1 is divisible by 4', k: '5ᵏ − 1 is divisible by 4, so 5ᵏ − 1 = 4q for some integer q', k1: '5ᵏ⁺¹ − 1 is divisible by 4' },
  base: [{ n: 0, inst: '5^0 − 1 = 0 = 0 × 4', simp: '0 = 0 × 4' }],
  lhs1: '5^(k+1) - 1', chain: [
    { rel: '=', e: '5 × 5^k - 1', why: 'alg' },
    { rel: '=', e: '5(4q + 1) - 1', why: 'ih', note: 'by P(k) (5ᵏ − 1 = 4q)' },
    { rel: '=', e: '20q + 4', why: 'alg' },
    { rel: '=', e: '4(5q + 1)', why: 'alg' }], cofactor: '5q + 1' });

add({ id: 'div-11', src: 'practice', title: '11ⁿ − 6 divisible by 5', kind: 'div', n0: 1,
  ask: 'Prove that 11ⁿ − 6 is divisible by 5 for all n ≥ 1.',
  div: { expr: '11^n - 6', d: 5, solveFor: '11^k = 5q + 6' },
  P: { n: '11ⁿ − 6 is divisible by 5', k: '11ᵏ − 6 = 5q for some integer q', k1: '11ᵏ⁺¹ − 6 is divisible by 5' },
  base: [{ n: 1, inst: '11^1 − 6 = 5 = 1 × 5', simp: '5 = 1 × 5' }],
  lhs1: '11^(k+1) - 6', chain: [
    { rel: '=', e: '11 × 11^k - 6', why: 'alg' },
    { rel: '=', e: '11(5q + 6) - 6', why: 'ih', note: 'by P(k) (11ᵏ = 5q + 6)' },
    { rel: '=', e: '55q + 60', why: 'alg' },
    { rel: '=', e: '5(11q + 12)', why: 'alg' }], cofactor: '11q + 12' });

add({ id: 'div-6', src: 'practice', title: '6ⁿ + 4 divisible by 5', kind: 'div', n0: 1,
  ask: 'Prove that 6ⁿ + 4 is divisible by 5 for all n ≥ 1.',
  div: { expr: '6^n + 4', d: 5, solveFor: '6^k = 5q − 4' },
  P: { n: '6ⁿ + 4 is divisible by 5', k: '6ᵏ + 4 = 5q for some integer q', k1: '6ᵏ⁺¹ + 4 is divisible by 5' },
  base: [{ n: 1, inst: '6^1 + 4 = 10 = 2 × 5', simp: '10 = 2 × 5' }],
  lhs1: '6^(k+1) + 4', chain: [
    { rel: '=', e: '6 × 6^k + 4', why: 'alg' },
    { rel: '=', e: '6(5q - 4) + 4', why: 'ih', note: 'by P(k) (6ᵏ = 5q − 4)' },
    { rel: '=', e: '30q - 20', why: 'alg' },
    { rel: '=', e: '5(6q - 4)', why: 'alg' }], cofactor: '6q - 4' });

add({ id: 'div-cube', src: 'practice', title: 'n³ − n divisible by 3', kind: 'div', n0: 1,
  ask: 'Prove that n³ − n is divisible by 3 for all n ≥ 1.',
  div: { expr: 'n^3 - n', d: 3, solveFor: 'k³ − k = 3q' },
  P: { n: 'n³ − n is divisible by 3', k: 'k³ − k = 3q for some integer q', k1: '(k + 1)³ − (k + 1) is divisible by 3' },
  base: [{ n: 1, inst: '1^3 − 1 = 0 = 0 × 3', simp: '0 = 0 × 3' }],
  lhs1: '(k+1)^3 - (k+1)', chain: [
    { rel: '=', e: 'k^3 + 3k^2 + 3k + 1 - k - 1', why: 'alg' },
    { rel: '=', e: '(k^3 - k) + 3k^2 + 3k', why: 'alg' },
    { rel: '=', e: '3q + 3k^2 + 3k', why: 'ih' },
    { rel: '=', e: '3(q + k^2 + k)', why: 'alg' }], cofactor: 'q + k^2 + k' });

// ---- parity
add({ id: 'odd-2024', src: '2024 Test 2 Q10', title: 'n² + n + 1 is odd', kind: 'parity', n0: 1,
  ask: 'Prove by mathematical induction that for all natural numbers n ≥ 1, n² + n + 1 is odd. (Hint: odd + even = odd.)',
  parity: { expr: 'n^2 + n + 1', odd: true },
  P: { n: 'n² + n + 1 is odd', k: 'k² + k + 1 is odd', k1: '(k + 1)² + (k + 1) + 1 is odd' },
  base: [{ n: 1, inst: '1² + 1 + 1 = 3', simp: '3 is odd' }],
  lhs1: '(k+1)^2 + (k+1) + 1', chain: [
    { rel: '=', e: 'k^2 + 2k + 1 + k + 1 + 1', why: 'alg' },
    { rel: '=', e: 'k^2 + 3k + 3', why: 'alg' },
    { rel: '=', e: '(k^2 + k + 1) + 2(k+1)', why: 'alg' }] });

add({ id: 'even-nn', src: 'practice', title: 'n² + n is even', kind: 'parity', n0: 1,
  ask: 'Prove by induction that n² + n is even for all n ≥ 1.',
  parity: { expr: 'n^2 + n', odd: false },
  P: { n: 'n² + n is even', k: 'k² + k is even', k1: '(k + 1)² + (k + 1) is even' },
  base: [{ n: 1, inst: '1² + 1 = 2', simp: '2 is even' }],
  lhs1: '(k+1)^2 + (k+1)', chain: [
    { rel: '=', e: 'k^2 + 2k + 1 + k + 1', why: 'alg' },
    { rel: '=', e: '(k^2 + k) + 2(k+1)', why: 'alg' }] });

add({ id: 'odd-3n', src: 'practice', title: '3ⁿ is odd', kind: 'parity', n0: 0,
  ask: 'Prove by induction that 3ⁿ is odd for all n ≥ 0.',
  parity: { expr: '3^n', odd: true },
  P: { n: '3ⁿ is odd', k: '3ᵏ is odd', k1: '3ᵏ⁺¹ is odd' },
  base: [{ n: 0, inst: '3^0 = 1', simp: '1 is odd' }],
  lhs1: '3^(k+1)', chain: [
    { rel: '=', e: '3 × 3^k', why: 'alg' },
    { rel: '=', e: '3^k + 2 × 3^k', why: 'alg' }] });

// ---- recurrences (ordinary induction)
const seqFns = {
  rabbits: { init: { 1: 25 }, f: (x, a) => A.mul(Qi(2), a(x - 1)), text: 'a₁ = 25, aₙ₊₁ = 2aₙ for n ≥ 1' },
  cubes: { init: { 1: 1 }, f: (x, a) => { const n = Qi(x - 1); return A.add(a(x - 1), A.add(A.add(A.mul(Qi(3), A.mul(n, n)), A.mul(Qi(3), n)), Qi(1))); }, text: 'a₁ = 1, aₙ₊₁ = aₙ + 3n² + 3n + 1 for n ≥ 1' },
  nn1: { init: { 1: 2 }, f: (x, a) => A.add(a(x - 1), A.mul(Qi(2), Qi(x))), text: 'a₁ = 2, aₙ₊₁ = aₙ + 2(n + 1) for n ≥ 1' },
  three: { init: { 1: 1 }, f: (x, a) => A.add(A.mul(Qi(3), a(x - 1)), Qi(2)), text: 'a₁ = 1, aₙ₊₁ = 3aₙ + 2 for n ≥ 1' },
  ind3: { init: { 1: 1, 2: 13 }, f: (x, a) => A.add(A.mul(Qi(-2), a(x - 1)), A.mul(Qi(3), a(x - 2))), text: 'a₁ = 1, a₂ = 13, aₙ₊₁ = −2aₙ + 3aₙ₋₁ for n > 1' },
  t24: { init: { 1: 3, 2: 5 }, f: (x, a) => A.add(a(x - 1), A.mul(Qi(2), a(x - 2))), text: 'a₁ = 3, a₂ = 5, aₙ₊₂ = aₙ₊₁ + 2aₙ for n ≥ 1' },
  t9q4: { init: { 0: 1, 1: 1, 2: 1 }, f: (x, a) => A.add(a(x - 1), a(x - 2)), text: 'a₀ = a₁ = a₂ = 1, aₙ = aₙ₋₁ + aₙ₋₂ for n ≥ 3' },
  fib: { init: { 1: 1, 2: 1 }, f: (x, a) => A.add(a(x - 1), a(x - 2)), text: 'F₁ = F₂ = 1, Fₙ₊₁ = Fₙ + Fₙ₋₁ for n ≥ 2 (written aₙ here)' },
};

add({ id: 'rec-rabbits', src: 'IND3 lecture example', title: 'Rabbits: aₙ = 25 × 2ⁿ⁻¹', kind: 'rec', n0: 1,
  ask: 'The rabbit population satisfies a₁ = 25 and aₙ₊₁ = 2aₙ for n ≥ 1. Prove that aₙ = 25 × 2ⁿ⁻¹ for all n ≥ 1.',
  seq: seqFns.rabbits, lhs: 'a(n)', rel: '=', rhs: '25 × 2^(n-1)',
  P: { n: 'aₙ = 25 × 2ⁿ⁻¹', k: 'aₖ = 25 × 2ᵏ⁻¹', k1: 'aₖ₊₁ = 25 × 2ᵏ' },
  base: [{ n: 1, inst: 'a_1 = 25 × 2^0', simp: '25 = 25' }],
  lhs1: 'a_{k+1}', chain: [
    { rel: '=', e: '2a_k', why: 'rec' },
    { rel: '=', e: '2(25 × 2^(k-1))', why: 'ih' },
    { rel: '=', e: '25 × 2^k', why: 'alg' }] });

add({ id: 'rec-cubes', src: 'Tutorial 9 Q3', title: 'aₙ = n³', kind: 'rec', n0: 1,
  ask: 'A sequence has a₁ = 1 and aₙ₊₁ = aₙ + 3n² + 3n + 1 for n ≥ 1. Show using induction that aₙ = n³ for all n ≥ 1.',
  seq: seqFns.cubes, lhs: 'a(n)', rel: '=', rhs: 'n^3',
  P: { n: 'aₙ = n³', k: 'aₖ = k³', k1: 'aₖ₊₁ = (k + 1)³' },
  base: [{ n: 1, inst: 'a_1 = 1^3', simp: '1 = 1' }],
  lhs1: 'a_{k+1}', chain: [
    { rel: '=', e: 'a_k + 3k^2 + 3k + 1', why: 'rec', note: 'since k ≥ 1' },
    { rel: '=', e: 'k^3 + 3k^2 + 3k + 1', why: 'ih' },
    { rel: '=', e: '(k+1)^3', why: 'alg' }] });

add({ id: 'rec-nn1', src: 'practice', title: 'aₙ = n(n + 1)', kind: 'rec', n0: 1,
  ask: 'A sequence has a₁ = 2 and aₙ₊₁ = aₙ + 2(n + 1) for n ≥ 1. Prove that aₙ = n(n + 1) for all n ≥ 1.',
  seq: seqFns.nn1, lhs: 'a(n)', rel: '=', rhs: 'n(n+1)',
  P: { n: 'aₙ = n(n + 1)', k: 'aₖ = k(k + 1)', k1: 'aₖ₊₁ = (k + 1)(k + 2)' },
  base: [{ n: 1, inst: 'a_1 = 1 × 2', simp: '2 = 2' }],
  lhs1: 'a_{k+1}', chain: [
    { rel: '=', e: 'a_k + 2(k+1)', why: 'rec' },
    { rel: '=', e: 'k(k+1) + 2(k+1)', why: 'ih' },
    { rel: '=', e: '(k+1)(k+2)', why: 'alg' }] });

add({ id: 'rec-three', src: 'practice', title: 'aₙ = 2 × 3ⁿ⁻¹ − 1', kind: 'rec', n0: 1,
  ask: 'A sequence has a₁ = 1 and aₙ₊₁ = 3aₙ + 2 for n ≥ 1. Prove that aₙ = 2 × 3ⁿ⁻¹ − 1 for all n ≥ 1.',
  seq: seqFns.three, lhs: 'a(n)', rel: '=', rhs: '2 × 3^(n-1) - 1',
  P: { n: 'aₙ = 2 × 3ⁿ⁻¹ − 1', k: 'aₖ = 2 × 3ᵏ⁻¹ − 1', k1: 'aₖ₊₁ = 2 × 3ᵏ − 1' },
  base: [{ n: 1, inst: 'a_1 = 2 × 3^0 − 1', simp: '1 = 1' }],
  lhs1: 'a_{k+1}', chain: [
    { rel: '=', e: '3a_k + 2', why: 'rec' },
    { rel: '=', e: '3(2 × 3^(k-1) - 1) + 2', why: 'ih' },
    { rel: '=', e: '2 × 3^k - 3 + 2', why: 'alg' },
    { rel: '=', e: '2 × 3^k - 1', why: 'alg' }] });

// ---- strong induction with recurrences
add({ id: 'strong-ind3', src: 'IND3 lecture example', title: 'aₙ = 4 + (−3)ⁿ', kind: 'rec', strong: true, n0: 1, nb: 2,
  ask: 'Let a₁ = 1, a₂ = 13 and aₙ₊₁ = −2aₙ + 3aₙ₋₁ for n > 1. Prove by induction that aₙ = 4 + (−3)ⁿ for all n ≥ 1.',
  seq: seqFns.ind3, lhs: 'a(n)', rel: '=', rhs: '4 + (-3)^n',
  P: { n: 'aₙ = 4 + (−3)ⁿ', k: 'aₖ = 4 + (−3)ᵏ', k1: 'aₖ₊₁ = 4 + (−3)ᵏ⁺¹' },
  base: [{ n: 1, inst: 'a_1 = 4 + (−3)^1', simp: '1 = 1' }, { n: 2, inst: 'a_2 = 4 + (−3)^2', simp: '13 = 4 + 9' }],
  lhs1: 'a_{k+1}', chain: [
    { rel: '=', e: '-2a_k + 3a_{k-1}', why: 'rec', note: 'since k ≥ 2' },
    { rel: '=', e: '-2(4 + (-3)^k) + 3(4 + (-3)^(k-1))', why: 'ihs', note: 'since P(k) and P(k − 1) are true' },
    { rel: '=', e: '-8 - 2(-3)^k + 12 + 3(-3)^(k-1)', why: 'alg' },
    { rel: '=', e: '4 - 2(-3)^k - (-3)^k', why: 'alg' },
    { rel: '=', e: '4 + (-3)(-3)^k', why: 'alg' },
    { rel: '=', e: '4 + (-3)^(k+1)', why: 'alg' }] });

add({ id: 'strong-2024', src: '2024 Test 2 Q11(b)', title: 'aₙ ≥ 2ⁿ', kind: 'rec', strong: true, n0: 1, nb: 2,
  ask: 'A sequence is defined by a₁ = 3, a₂ = 5 and aₙ₊₂ = aₙ₊₁ + 2aₙ for n ≥ 1. Use strong induction to show that aₙ ≥ 2ⁿ for all n ≥ 1.',
  seq: seqFns.t24, lhs: 'a(n)', rel: '≥', rhs: '2^n',
  P: { n: 'aₙ ≥ 2ⁿ', k: 'aₖ ≥ 2ᵏ', k1: 'aₖ₊₁ ≥ 2ᵏ⁺¹' },
  base: [{ n: 1, inst: 'a_1 ≥ 2^1', simp: '3 ≥ 2' }, { n: 2, inst: 'a_2 ≥ 2^2', simp: '5 ≥ 4' }],
  lhs1: 'a_{k+1}', chain: [
    { rel: '=', e: 'a_k + 2a_{k-1}', why: 'rec', note: 'since k − 1 ≥ 1, so the recurrence formula applies' },
    { rel: '≥', e: '2^k + 2 × 2^(k-1)', why: 'ihs', note: 'by P(k) and P(k − 1), both true since k − 1 ≥ 1' },
    { rel: '=', e: '2^k + 2^k', why: 'alg' },
    { rel: '=', e: '2^(k+1)', why: 'alg' }] });

add({ id: 'strong-t9q4', src: 'Tutorial 9 Q4', title: 'aₙ₊₂ ≥ (√2)ⁿ', kind: 'rec', strong: true, n0: 0, nb: 3,
  ask: 'Let a₀ = a₁ = a₂ = 1 and aₙ = aₙ₋₁ + aₙ₋₂ for n ≥ 3. Prove by strong induction that aₙ₊₂ ≥ (√2)ⁿ for all n ≥ 0.',
  seq: seqFns.t9q4, lhs: 'a(n+2)', rel: '≥', rhs: 'sqrt(2)^n',
  P: { n: 'aₙ₊₂ ≥ (√2)ⁿ', k: 'aₖ₊₂ ≥ (√2)ᵏ', k1: 'aₖ₊₃ ≥ (√2)ᵏ⁺¹' },
  base: [{ n: 0, inst: 'a_2 ≥ sqrt(2)^0', simp: '1 ≥ 1' }, { n: 1, inst: 'a_3 ≥ sqrt(2)^1', simp: '2 ≥ √2' }, { n: 2, inst: 'a_4 ≥ sqrt(2)^2', simp: '3 ≥ 2' }],
  lhs1: 'a_{k+3}', chain: [
    { rel: '=', e: 'a_{k+2} + a_{k+1}', why: 'rec' },
    { rel: '≥', e: 'sqrt(2)^k + sqrt(2)^(k-1)', why: 'ihs' },
    { rel: '=', e: '(sqrt(2) + 1)sqrt(2)^(k-1)', why: 'alg' },
    { rel: '≥', e: '2 × sqrt(2)^(k-1)', why: 'since', note: 'since √2 + 1 ≥ 2' },
    { rel: '=', e: 'sqrt(2)^2 × sqrt(2)^(k-1)', why: 'alg' },
    { rel: '=', e: 'sqrt(2)^(k+1)', why: 'alg' }],
  note: 'The official solution checks P(0), P(1) and P(2), one base case per initial value a₀, a₁, a₂ (as IND3 says), and starts (R) at k ≥ 2. Two base cases would be enough mathematically, since the step only uses P(k) and P(k − 1).' });

add({ id: 'strong-fib', src: 'practice', title: 'Fibonacci: aₙ < 2ⁿ', kind: 'rec', strong: true, n0: 1, nb: 2,
  ask: 'Let a₁ = a₂ = 1 and aₙ₊₁ = aₙ + aₙ₋₁ for n ≥ 2. Prove by strong induction that aₙ < 2ⁿ for all n ≥ 1.',
  seq: seqFns.fib, lhs: 'a(n)', rel: '<', rhs: '2^n',
  P: { n: 'aₙ < 2ⁿ', k: 'aₖ < 2ᵏ', k1: 'aₖ₊₁ < 2ᵏ⁺¹' },
  base: [{ n: 1, inst: 'a_1 < 2^1', simp: '1 < 2' }, { n: 2, inst: 'a_2 < 2^2', simp: '1 < 4' }],
  lhs1: 'a_{k+1}', chain: [
    { rel: '=', e: 'a_k + a_{k-1}', why: 'rec', note: 'since k ≥ 2' },
    { rel: '<', e: '2^k + 2^(k-1)', why: 'ihs' },
    { rel: '<', e: '2^k + 2^k', why: 'alg' },
    { rel: '=', e: '2^(k+1)', why: 'alg' }] });

// ---- stamps (strong induction)
add({ id: 'stamps-38', src: 'IND2 lecture example', title: '3c and 8c stamps', kind: 'stamps', strong: true, n0: 14, nb: 3,
  ask: 'The country of Oz issues only 3-cent and 8-cent stamps. Show that any amount of postage of 14 cents or more is possible.',
  stamps: { a: 3, b: 8 } });
add({ id: 'stamps-45', src: 'Tutorial 9 Q2', title: '4c and 5c stamps', kind: 'stamps', strong: true, n0: 12, nb: 4,
  ask: 'Prove by strong induction that every integer n ≥ 12 can be written as n = 4x + 5y for some non-negative integers x, y.',
  stamps: { a: 4, b: 5 } });

export const BANK = B;
export const byId = Object.fromEntries(B.map((p) => [p.id, p]));

// ---------------------------------------------------------------- generated problems
export function generated(kind, seed) {
  const rng = new Rng(seed);
  if (kind === 'stamps') {
    const pairs = [[3, 5], [3, 7], [2, 5], [3, 4], [4, 7], [5, 6], [3, 10], [2, 7], [4, 9], [5, 7]];
    const [a, b] = rng.pick(pairs);
    const n0 = a * b - a - b + 1;
    return { id: `stamps-${a}${b}`, src: 'generated', title: `${a}c and ${b}c stamps`, kind: 'stamps', strong: true, n0, nb: a,
      ask: `A post office only sells ${a}-cent and ${b}-cent stamps. Prove by strong induction that every amount of ${n0} cents or more can be made exactly.`, stamps: { a, b } };
  }
  if (kind === 'div') {
    const opts = [[3, 2, -1, 0], [7, 6, -1, 0], [9, 8, -1, 0], [4, 3, -1, 1], [6, 5, -1, 0], [7, 3, -1, 1], [9, 4, -1, 0], [13, 4, -1, 0], [8, 7, -1, 1], [11, 10, -1, 0], [5, 2, 1, 1], [7, 2, 1, 1], [3, 2, 1, 1], [9, 4, 3, 1], [7, 3, 2, 1]];
    const [a, d, c, n0] = rng.pick(opts);
    const cs = c < 0 ? `− ${-c}` : `+ ${c}`;
    const ce = c < 0 ? ` - ${-c}` : ` + ${c}`;
    const base0 = a ** n0 + c;
    // a^k + c = dq  =>  a^k = dq - c
    const solve = c < 0 ? `${a}ᵏ = ${d}q + ${-c}` : `${a}ᵏ = ${d}q − ${c}`;
    const inner = c < 0 ? `${d}q + ${-c}` : `${d}q - ${c}`;
    const constTerm = a * -c + c; // a(dq - c) + c = adq + c(1 - a)
    const k2 = constTerm / d;
    const ce2 = constTerm < 0 ? ` - ${-constTerm}` : ` + ${constTerm}`;
    const cf = k2 < 0 ? `${a}q - ${-k2}` : `${a}q + ${k2}`;
    return { id: `div-${a}-${d}-${c}-${n0}`, src: 'generated', title: `${a}ⁿ ${cs} divisible by ${d}`, kind: 'div', n0,
      ask: `Prove that ${a}ⁿ ${cs} is divisible by ${d} for all n ≥ ${n0}.`,
      div: { expr: `${a}^n${ce}`, d, solveFor: solve },
      P: { n: `${a}ⁿ ${cs} is divisible by ${d}`, k: `${a}ᵏ ${cs} = ${d}q for some integer q`, k1: `${a}ᵏ⁺¹ ${cs} is divisible by ${d}` },
      base: [{ n: n0, inst: `${a}^${n0}${ce} = ${base0} = ${base0 / d} × ${d}`, simp: `${base0} = ${base0 / d} × ${d}` }],
      lhs1: `${a}^(k+1)${ce}`, chain: [
        { rel: '=', e: `${a} × ${a}^k${ce}`, why: 'alg' },
        { rel: '=', e: `${a}(${inner})${ce}`, why: 'ih', note: `by P(k) (${solve})` },
        { rel: '=', e: `${a * d}q${ce2}`, why: 'alg' },
        { rel: '=', e: `${d}(${cf})`, why: 'alg' }], cofactor: cf };
  }
  if (kind === 'recur') {
    // a_n = A r^n + B s^n with a_{n+1} = (r+s) a_n − rs a_{n−1}
    const combos = [[1, 2, 1, 1], [1, 3, -1, 2], [1, 2, 1, -1], [1, 3, 1, 1], [2, 3, -1, 2], [1, -3, 4, 1], [-1, 2, 5, 1], [1, -2, 3, 1], [3, 2, -2, 1]];
    const [Ac, r, Bc, s] = rng.pick(combos);
    const p = r + s, q = -r * s;
    const term = (n) => Ac * r ** n + Bc * s ** n;
    const a1 = term(1), a2 = term(2);
    const fmt = (coef, base, e) => {
      const pw = base === 1 ? '' : base < 0 ? `(${base})^${e}` : `${base}^${e}`;
      if (base === 1) return String(coef);
      if (coef === 1) return pw; if (coef === -1) return `-${pw}`;
      return `${coef} × ${pw}`;
    };
    const closed = (e) => [fmt(Ac, r, e), fmt(Bc, s, e)].join(' + ').replace('+ -', '- ');
    const c1 = (c) => (c === 1 ? '' : c === -1 ? '-' : String(c));
    const c2 = (c) => (Math.abs(c) === 1 ? '' : String(Math.abs(c)));
    const seq = { init: { 1: a1, 2: a2 }, f: (x, a) => A.add(A.mul(Qi(p), a(x - 1)), A.mul(Qi(q), a(x - 2))), text: `a₁ = ${a1}, a₂ = ${a2}, aₙ₊₁ = ${c1(p).replace('-', '−')}aₙ ${q < 0 ? '−' : '+'} ${c2(q)}aₙ₋₁ for n ≥ 2` };
    const recE = `${c1(p)}a_k ${q < 0 ? '-' : '+'} ${c2(q)}a_{k-1}`;
    const ihE = `${c1(p)}(${closed('k')}) ${q < 0 ? '-' : '+'} ${c2(q)}(${closed('(k-1)')})`;
    const txt = (e) => closed(e).replace(/\^\(k-1\)/g, 'ᵏ⁻¹').replace(/\^k/g, 'ᵏ').replace(/\^n/g, 'ⁿ').replace(/\^\(k\+1\)/g, 'ᵏ⁺¹').replace(/ - /g, ' − ').replace(/\(-/g, '(−');
    return { id: `gen-rec-${Ac}${r}${Bc}${s}`, src: 'generated', title: `aₙ = ${txt('n')}`, kind: 'rec', strong: true, n0: 1, nb: 2,
      ask: `A sequence is defined by ${seq.text}. Prove by strong induction that aₙ = ${txt('n')} for all n ≥ 1.`,
      seq, lhs: 'a(n)', rel: '=', rhs: closed('n'),
      P: { n: `aₙ = ${txt('n')}`, k: `aₖ = ${txt('k')}`, k1: `aₖ₊₁ = ${txt('(k+1)')}` },
      base: [{ n: 1, inst: `a_1 = ${closed('1')}`, simp: `${a1} = ${a1}` }, { n: 2, inst: `a_2 = ${closed('2')}`, simp: `${a2} = ${a2}` }],
      lhs1: 'a_{k+1}', chain: [
        { rel: '=', e: recE, why: 'rec', note: 'since k ≥ 2' },
        { rel: '=', e: ihE, why: 'ihs', note: 'since P(k) and P(k − 1) are true' },
        { rel: '=', e: closed('(k+1)'), why: 'alg' }] };
  }
  return null;
}

// ---------------------------------------------------------------- evaluation helpers
export function functionsFor(prob) {
  const fns = {};
  if (prob.sum) {
    const term = A.parseExpr(prob.sum.term);
    const cache = new Map();
    fns.S = (x) => {
      const n = Number(x.n ?? x.f);
      if (cache.has(n)) return cache.get(n);
      let s = Qi(0);
      for (let i = prob.sum.from; i <= n; i++) s = A.add(s, A.evaluate(term, { i: Qi(i) }));
      cache.set(n, s);
      return s;
    };
    fns.termAt = (i) => A.evaluate(term, { i: Qi(i) });
  }
  if (prob.seq) {
    const memo = new Map(Object.entries(prob.seq.init).map(([k, v]) => [Number(k), Qi(v)]));
    const a = (x) => {
      if (memo.has(x)) return memo.get(x);
      if (x < Math.min(...Object.keys(prob.seq.init).map(Number))) throw new A.ExprError(`a_${x} is not defined.`, 0);
      const v = prob.seq.f(x, a);
      memo.set(x, v);
      return v;
    };
    fns.a = (x) => { if (x.d !== 1n) throw new A.ExprError('Sequence indices must be whole numbers.', 0); return a(Number(x.n)); };
    fns.F = fns.a;
    fns.u = fns.a;
  }
  return fns;
}

export function envFor(prob, k) {
  const env = { k: Qi(k) };
  if (prob.div) {
    const e = A.parseExpr(prob.div.expr);
    env.q = A.div(A.evaluate(e, { n: Qi(k) }), Qi(prob.div.d));
  }
  return env;
}

export const kRange = (prob) => {
  const kmin = prob.n0 + (prob.nb || 1) - 1;
  const ks = [];
  for (let k = kmin; k < kmin + 14; k++) ks.push(k);
  ks.push(kmin + 23, kmin + 37);
  return ks;
};

// Value of a target side of P at index x
export function sideAt(prob, side, x) {
  const e = A.parseExpr(side === 'L' ? prob.lhs : prob.rhs);
  return A.evaluate(e, { n: Qi(x) }, functionsFor(prob));
}

// ---------------------------------------------------------------- checks
const normRel = (r) => ({ '>=': '≥', '<=': '≤' }[r] || r);
const flip = { '≥': '≤', '≤': '≥', '>': '<', '<': '>', '=': '=', '≠': '≠' };

// Check a statement P(v) typed by the student. v = 'n' | 'k' | 'k+1'
export function checkStatement(prob, text, v) {
  if (prob.kind === 'div' || prob.kind === 'parity' || prob.kind === 'stamps') return { ok: true, skip: true };
  let rel;
  try { rel = A.parseRelation(text); } catch (e) { return { ok: false, message: e.message }; }
  const fns = functionsFor(prob);
  const varName = v === 'n' ? 'n' : 'k';
  const offset = v === 'k+1' ? 1 : 0;
  const evalSide = (node, x) => {
    if (node.t === 'sumdots') {
      if (!prob.sum) throw new A.ExprError('This statement has no sum in it.', 0);
      const lastVal = A.evaluate(node.last, { [varName]: Qi(x), n: Qi(x), k: Qi(x) }, fns);
      let top = null;
      for (let i = prob.sum.from; i <= x + 3; i++) if (A.cmp(fns.termAt(i), lastVal) === 0) top = i;
      if (top === null) throw new A.ExprError('The last term of the sum doesn’t match the question’s sum.', 0);
      (node.tail || []).forEach((t, j) => {
        const want = fns.termAt(top - node.tail.length + j);
        if (A.cmp(A.evaluate(t, { [varName]: Qi(x), n: Qi(x), k: Qi(x) }, fns), want) !== 0) throw new A.ExprError('The terms just before the last one don’t match the sum.', 0);
      });
      node.head.forEach((h, idx) => {
        if (A.cmp(A.evaluate(h, {}, fns), fns.termAt(prob.sum.from + idx)) !== 0) throw new A.ExprError(`The sum's term ${idx + 1} should be ${A.show(fns.termAt(prob.sum.from + idx))}.`, 0);
      });
      return fns.S(Qi(top));
    }
    return A.evaluate(node, { [varName]: Qi(x) }, fns);
  };
  // the statement must mention the sequence term / the sum itself, not just an equal value
  const mentions = (node) => node.t === 'sumdots' || [...A.callsIn(node)].some((f) => f !== 'sqrt');
  if ((prob.seq || prob.sum) && !mentions(rel.lhs) && !mentions(rel.rhs)) {
    const sym = prob.sum ? 'the sum (1 + 2 + ⋯ or S(n))' : prob.lhs?.includes('n+2') ? 'a_{n+2}' : 'aₙ (type a_n)';
    return { ok: false, message: `P(${v}) is a statement about ${sym.replace(/n/g, varName === 'k' ? (v === 'k+1' ? 'k+1' : 'k') : 'n')}: write it in.` };
  }
  if ((prob.seq || prob.sum) && mentions(rel.lhs) && mentions(rel.rhs)) {
    return { ok: false, message: prob.sum ? `P(${v}) should have the sum on one side and its formula, with no sums in it, on the other. Splitting off the last term comes later, in the working.` : `P(${v}) should have the sequence term on one side and the formula, with no sequence terms in it, on the other. The recurrence isn’t P(${v}): you use it later, in the working.` };
  }
  const seqSide = mentions(rel.lhs) ? rel.lhs : rel.rhs;
  if ((prob.seq || prob.sum) && seqSide.t !== 'sumdots') {
    // the term must be the right one: aₙ (or aₙ₊₂, S(n) …) at this n, not an earlier one
    const side = seqSide;
    const want = new Set(), have = new Set();
    try {
      const x0 = Math.max(prob.n0, 1) + 3;
      const idx = (node, env) => { const out = []; (function w(n) { if (!n) return; if (n.t === 'call' && n.f !== 'sqrt') out.push(A.show(A.evaluate(n.args[0], env, fns))); for (const c of [n.a, n.b, ...(n.args || [])]) if (c) w(c); })(node); return out; };
      for (const i of idx(A.parseExpr(prob.lhs), { n: Qi(x0 + (v === 'k+1' ? 1 : 0)) })) want.add(i);
      for (const i of idx(side, { [varName]: Qi(x0) })) have.add(i);
    } catch { /* fall through to the numeric check */ }
    if (want.size && (have.size !== want.size || [...have].some((i) => !want.has(i)))) return { ok: false, message: wrongMsg(v) };
  }
  let r = normRel(rel.rel);
  let L = rel.lhs, R = rel.rhs;
  if (r === '≤' || r === '<') { [L, R] = [R, L]; r = flip[r]; }
  let tr = prob.rel;
  let tL = A.parseExpr(prob.lhs), tR = A.parseExpr(prob.rhs);
  if (tr === '≤' || tr === '<') { [tL, tR] = [tR, tL]; tr = flip[tr]; }
  if (r !== tr) return { ok: false, message: `The relation should be “${tr}”${prob.rel !== tr ? ` (or “${prob.rel}” the other way round)` : ''}, not “${rel.rel}”.` };
  const lo = Math.max(prob.n0, 1) + 1;
  if (r === '=') {
    // an equation that holds for every n can't be checked by truth alone: each side must be the question's side
    let firstErr = null;
    for (const [S1, S2] of [[L, R], [R, L]]) {
      try {
        let ok = true;
        for (let x = lo; x < lo + 7 && ok; x++) {
          const a = A.evaluate(tL, { n: Qi(x + offset) }, fns), b = A.evaluate(tR, { n: Qi(x + offset) }, fns);
          if (A.cmp(evalSide(S1, x), a) !== 0 || A.cmp(evalSide(S2, x), b) !== 0) ok = false;
        }
        if (ok) return { ok: true };
      } catch (e) { firstErr = firstErr || e.message; }
    }
    if (firstErr && !/doesn’t match|should be/.test(firstErr)) return { ok: false, message: firstErr.includes("don't know") ? `${firstErr} Write P(${v}) using ${varName} only.` : firstErr };
    return { ok: false, message: wrongMsg(v) };
  }
  let ratio = null;
  try {
    for (let x = lo; x < lo + 9; x++) {
      const target = A.sub(A.evaluate(tL, { n: Qi(x + offset) }, fns), A.evaluate(tR, { n: Qi(x + offset) }, fns));
      const mine = A.sub(evalSide(L, x), evalSide(R, x));
      if (A.cmp(target, Qi(0)) === 0) { if (A.cmp(mine, Qi(0)) !== 0) return { ok: false, message: wrongMsg(v) }; continue; }
      const rr = A.div(mine, target);
      if (ratio === null) ratio = rr;
      if (A.cmp(rr, ratio) !== 0 || A.cmp(rr, Qi(0)) <= 0 && r !== '=') return { ok: false, message: wrongMsg(v) };
      if (r === '=' && A.cmp(rr, Qi(0)) === 0) return { ok: false, message: wrongMsg(v) };
    }
  } catch (e) { return { ok: false, message: e.message.includes("don't know") ? `${e.message} Write P(${v}) using ${varName} only.` : e.message }; }
  return { ok: true };
}
function wrongMsg(v) {
  return v === 'n' ? 'That isn’t the statement you were asked to prove.' : v === 'k' ? 'That isn’t P(k): substitute k for n everywhere.' : 'That isn’t P(k + 1): substitute k + 1 for n everywhere (brackets!).';
}

// Base case: student types the instance (any numeric form). Returns ok when it is the right instance and true.
export function checkBase(prob, n, text) {
  if (prob.kind === 'div' || prob.kind === 'parity' || prob.kind === 'stamps') return { ok: true, skip: true };
  let rel;
  try { rel = A.parseRelation(text.replace(/\bn\b/g, String(n))); } catch (e) { return { ok: false, message: e.message }; }
  const fns = functionsFor(prob);
  let L, R;
  try { L = A.evaluate(rel.lhs, {}, fns); R = A.evaluate(rel.rhs, {}, fns); } catch (e) { return { ok: false, message: e.message.includes("don't know") ? 'Use numbers only here: substitute n = ' + n + '.' : e.message }; }
  const tL = sideAt(prob, 'L', n), tR = sideAt(prob, 'R', n);
  const r = normRel(rel.rel);
  const matches = (A.cmp(L, tL) === 0 && A.cmp(R, tR) === 0 && r === prob.rel) || (A.cmp(L, tR) === 0 && A.cmp(R, tL) === 0 && r === flip[prob.rel]);
  if (!matches) return { ok: false, message: `P(${n}) should compare ${A.show(tL)} and ${A.show(tR)} with “${prob.rel}”.` };
  return { ok: true, message: `P(${n}) says ${A.show(tL)} ${prob.rel} ${A.show(tR)}, which is true.` };
}

// The chain of (k+1)-side working.
export function checkChain(prob, lines) {
  const fns = functionsFor(prob);
  const ks = kRange(prob);
  const env = (k) => envFor(prob, k);
  const results = [];
  const parsed = [];
  for (const [i, l] of lines.entries()) {
    try { parsed.push(A.parseExpr(l.e)); } catch (e) { results.push({ ok: false, message: e.message }); return { ok: false, results, stopAt: i }; }
    const used = A.varsIn(parsed[i]);
    const allowed = new Set(['k', ...(prob.div ? ['q'] : [])]);
    const bad = [...used].filter((v) => !allowed.has(v));
    if (bad.length) { results.push({ ok: false, message: bad.includes('n') ? 'Work with k here (n is only used in the statement P(n)).' : `What is “${bad[0]}”? Only k${prob.div ? ' and q' : ''} can appear here.` }); return { ok: false, results, stopAt: i }; }
    if (i === 0) {
      const start = A.parseExpr(prob.lhs1);
      const h = A.holdsOver(parsed[0], '=', start, ks, env, fns);
      if (!h.ok) { results.push({ ok: false, message: h.error ?? `Start from the left-hand side of P(k + 1), which is ${A.pretty(start)}.` }); return { ok: false, results, stopAt: 0 }; }
      results.push({ ok: true });
      continue;
    }
    const rel = normRel(l.rel);
    const h = A.holdsOver(parsed[i - 1], rel, parsed[i], ks, env, fns);
    if (!h.ok) {
      const msg = h.error ? h.error : `This “${rel}” is false: when k = ${h.k}, the previous line equals ${A.show(h.a)} but this line equals ${A.show(h.b)}.`;
      results.push({ ok: false, message: msg }); return { ok: false, results, stopAt: i };
    }
    // a hypothesis step should actually remove S(k) / a_k
    if ((l.why === 'ih' || l.why === 'ihs') && prob.sum && A.callsIn(parsed[i - 1]).has('S') && A.callsIn(parsed[i]).has('S')) {
      results.push({ ok: false, message: 'Using P(k) here means replacing the sum up to k by its formula.' }); return { ok: false, results, stopAt: i };
    }
    const why = reasonProblem(prob, l.why, parsed[i - 1], parsed[i], ks, fns);
    if (why) { results.push({ ok: false, message: why }); return { ok: false, results, stopAt: i }; }
    results.push({ ok: true });
  }
  // end condition
  const last = parsed[parsed.length - 1];
  const rels = lines.slice(1).map((l) => normRel(l.rel));
  const usesIH = lines.some((l) => l.why === 'ih' || l.why === 'ihs');
  const overall = { ok: false, done: false, message: '' };
  if (prob.kind === 'div') {
    const cof = lastFactorOf(last, prob.div.d);
    if (!cof) { overall.message = `Keep going until the last line is written as ${prob.div.d} × (an integer expression).`; return { ok: true, results, overall }; }
    if (A.callsIn(cof).size || hasDivision(cof)) { overall.message = 'The bracket must clearly be an integer (no fractions).'; return { ok: true, results, overall }; }
    if (!A.varsIn(cof).has('q') && !A.varsIn(last).has('q') && !lines.some((l) => /q/.test(l.e))) { overall.message = 'Use the hypothesis: write the old expression in terms of q.'; return { ok: true, results, overall }; }
  } else if (prob.kind === 'parity') {
    const split = parityForm(last, prob, fns);
    if (!split.ok) { overall.message = split.message; return { ok: true, results, overall }; }
  } else {
    const target = A.parseExpr(prob.rhs);
    const h = A.holdsOver(last, '=', target, ks, (k) => ({ ...env(k), n: Qi(k + 1) }), fns);
    if (!h.ok) { overall.message = `Keep going until you reach the right-hand side of P(k + 1), ${showE(subst(prob.rhs, '(k+1)'))}.`; return { ok: true, results, overall }; }
    const goal = prob.rel;
    const has = (r) => rels.includes(r);
    if (goal === '=' && rels.some((r) => r !== '=')) { overall.message = 'To prove an equation every step must be “=”.'; return { ok: true, results, overall }; }
    if ((goal === '≥' || goal === '>') && (has('≤') || has('<'))) { overall.message = 'Mixing ≥ and ≤ in one chain proves nothing.'; return { ok: true, results, overall }; }
    if ((goal === '≤' || goal === '<') && (has('≥') || has('>'))) { overall.message = 'Mixing ≤ and ≥ in one chain proves nothing.'; return { ok: true, results, overall }; }
    if (goal === '>' && !has('>')) { overall.message = 'You need a strict “>” somewhere to prove “>”.'; return { ok: true, results, overall }; }
    if (goal === '<' && !has('<')) { overall.message = 'You need a strict “<” somewhere to prove “<”.'; return { ok: true, results, overall }; }
  }
  if (!usesIH && prob.kind !== 'parity') { overall.message = 'Every line is right, but you haven’t marked where you used the inductive hypothesis. An induction proof must use P(k) (mark that line “by P(k)”).'; return { ok: true, results, overall }; }
  overall.ok = true; overall.done = true;
  overall.message = prob.kind === 'div' ? `So the expression is ${prob.div.d} × an integer, i.e. divisible by ${prob.div.d}: P(k + 1) is true.` : prob.kind === 'parity' ? `${prob.parity.odd ? 'Odd + even is odd' : 'Even + even is even'}, so P(k + 1) is true.` : 'That reaches P(k + 1).';
  return { ok: true, results, overall };
}

// ---- does each step's reason fit what the step does?
const FN_ALIAS = { F: 'a', u: 'a' };
function callKeys(node, k, prob, fns) {
  const out = new Set();
  (function walk(n) {
    if (!n) return;
    if (n.t === 'call' && n.f !== 'sqrt') {
      let idx = '?';
      try { idx = A.show(A.evaluate(n.args[0], envFor(prob, k), fns)); } catch { /* unknown index */ }
      out.add(`${FN_ALIAS[n.f] || n.f}@${idx}`);
    }
    for (const c of [n.a, n.b, ...(n.args || [])]) if (c) walk(c);
  })(node);
  return out;
}
// The quantities P(k) (and P(k − 1)) talk about, which must be visible before “by P(k)”.
function hypothesisTerms(prob) {
  if (prob.kind === 'div') {
    const m = /^(\d+)\^n/.exec(prob.div.expr);
    return [m ? `${m[1]}^k` : null, subst(prob.div.expr, 'k')].filter(Boolean);
  }
  if (prob.kind === 'parity' || prob.kind === 'stamps' || !prob.lhs) return [];
  const out = [subst(prob.lhs, 'k')];
  if (prob.strong) out.push(subst(prob.lhs, '(k-1)'));
  return out;
}
function showsTerm(node, terms, prob, fns) {
  const ks = kRange(prob).slice(0, 6);
  const env = (k) => envFor(prob, k);
  const H = terms.map((t) => A.parseExpr(t));
  const isH = (x) => H.some((h) => A.holdsOver(x, '=', h, ks, env, fns).ok);
  const subs = [];
  (function walk(n) { if (!n) return; subs.push(n); for (const c of [n.a, n.b, ...(n.args || [])]) if (c) walk(c); })(node);
  if (subs.some(isH)) return true;
  // or a group of the added terms, e.g. k² − 7k + 12 inside k² − 7k + 12 + 2k − 6
  const parts = [];
  (function flat(n, sign) {
    if (n.t === 'add') { flat(n.a, sign); flat(n.b, sign); } else if (n.t === 'sub') { flat(n.a, sign); flat(n.b, -sign); } else parts.push(sign > 0 ? n : { t: 'neg', a: n });
  })(node, 1);
  if (parts.length < 3 || parts.length > 10) return false;
  for (let mask = 1; mask < (1 << parts.length) - 1; mask++) {
    let e = null;
    parts.forEach((p, i) => { if (mask & (1 << i)) e = e ? { t: 'add', a: e, b: p } : p; });
    if (isH(e)) return true;
  }
  return false;
}
function reasonProblem(prob, why, prev, cur, ks, fns) {
  if (prob.seq || prob.sum) {
    const k = ks[Math.min(3, ks.length - 1)];
    const before = callKeys(prev, k, prob, fns), after = callKeys(cur, k, prob, fns);
    const changed = before.size !== after.size || [...before].some((x) => !after.has(x));
    if ((why === 'alg' || why === 'since' || why === 'part') && changed) {
      return prob.sum ? 'Algebra alone can’t change which sums appear. Splitting off the last term is “split the sum”; replacing the sum up to k is “by P(k)”.'
        : 'Algebra alone can’t change which terms of the sequence appear. Expanding aₖ₊₁ is “by the recurrence”; replacing aₖ is “by P(k)”.';
    }
    if ((why === 'rec' || why === 'split') && ![...before].some((x) => !after.has(x))) {
      return why === 'rec' ? 'This step doesn’t use the recurrence: it should replace the highest term (like aₖ₊₁) by earlier ones.' : 'This step doesn’t split the sum: write the sum up to k + 1 as the sum up to k plus the last term.';
    }
  }
  if (why === 'ih' || why === 'ihs') {
    const terms = hypothesisTerms(prob);
    if (terms.length && !showsTerm(prev, terms, prob, fns)) {
      return `Before you can use P(k), the previous line has to contain what P(k) is about, ${showE(terms[0])}${prob.kind === 'ineq' ? ' (group it in brackets, as the lecturer does)' : ''}. Rewrite the line so it appears, then replace it using P(k).`;
    }
  }
  return null;
}

function lastFactorOf(node, d) {
  if (node.t !== 'mul') return null;
  const isD = (x) => x.t === 'num' && A.cmp(x.v, Qi(d)) === 0;
  if (isD(node.a)) return node.b;
  if (isD(node.b)) return node.a;
  return null;
}
function hasDivision(n) { if (n.t === 'div') return true; return [n.a, n.b, ...(n.args || [])].some((c) => c && hasDivision(c)); }

function parityForm(node, prob, fns) {
  const want = prob.parity.odd ? 'odd' : 'even';
  if (node.t !== 'add') return { ok: false, message: `Finish with a line of the form (the expression from P(k)) + 2 × (something), then say ${want} + even is ${want}.` };
  const prevE = A.parseExpr(prob.parity.expr);
  const ks = kRange(prob);
  const env = (k) => ({ k: Qi(k), n: Qi(k) });
  for (const [x, y] of [[node.a, node.b], [node.b, node.a]]) {
    if (A.holdsOver(x, '=', prevE, ks, env, fns).ok) {
      const isTwo = (t) => t.t === 'mul' && ((t.a.t === 'num' && A.cmp(t.a.v, Qi(2)) === 0) || (t.b.t === 'num' && A.cmp(t.b.v, Qi(2)) === 0));
      if (isTwo(y)) return { ok: true };
      return { ok: false, message: 'Write the other part as 2 × (an integer) so it is obviously even.' };
    }
  }
  return { ok: false, message: `One part of the last line must be exactly ${showE(subst(prob.parity.expr, 'k'))} (which P(k) says is ${want}).` };
}

// Stamp problems: base representations and the step.
export function stampBases(prob) {
  const { a, b } = prob.stamps;
  const out = [];
  for (let n = prob.n0; n < prob.n0 + a; n++) {
    let rep = null;
    for (let y = 0; y * b <= n && !rep; y++) if ((n - y * b) % a === 0) rep = { x: (n - y * b) / a, y };
    out.push({ n, ...rep });
  }
  return out;
}
export function checkStampRep(prob, n, x, y) {
  const { a, b } = prob.stamps;
  x = Number(x); y = Number(y);
  if (!Number.isInteger(x) || !Number.isInteger(y) || x < 0 || y < 0) return { ok: false, message: 'x and y must be whole numbers ≥ 0.' };
  if (a * x + b * y !== n) return { ok: false, message: `${a} × ${x} + ${b} × ${y} = ${a * x + b * y}, not ${n}.` };
  return { ok: true };
}

// ---------------------------------------------------------------- model proof text
export function modelProof(prob) {
  const L = [];
  const strongName = prob.strong ? 'strong induction' : 'induction';
  if (prob.kind === 'stamps') {
    const { a, b } = prob.stamps;
    const bases = stampBases(prob);
    const top = prob.n0 + a - 1;
    L.push(`For n ≥ ${prob.n0}, let P(n) be the predicate that “n = ${a}x + ${b}y for some integers x, y ≥ 0”.`);
    L.push(`(B) ${bases.map((r) => `P(${r.n}): ${r.n} = ${a} × ${r.x} + ${b} × ${r.y}`).join(';  ')}. All true.`);
    L.push(`(R) Suppose k ≥ ${top} is such that P(${prob.n0}), P(${prob.n0 + 1}), …, P(k) are all true. We show P(k + 1) is true.`);
    L.push(`k + 1 = (k + 1 − ${a}) + ${a} = (k − ${a - 1}) + ${a}. Since k ≥ ${top}, k − ${a - 1} ≥ ${prob.n0}, and k − ${a - 1} < k, so P(k − ${a - 1}) is true by the inductive assumption.`);
    L.push(`So k − ${a - 1} = ${a}x + ${b}y for some integers x, y ≥ 0, and then k + 1 = ${a}x + ${b}y + ${a} = ${a}(x + 1) + ${b}y, where x + 1, y ≥ 0 are integers. So P(k + 1) is true.`);
    L.push(`Hence by strong induction (the second principle of induction), P(n) is true for all n ≥ ${prob.n0}. □`);
    return L;
  }
  L.push(`For n ≥ ${prob.n0}, let P(n) be the predicate that “${prob.P.n}”.`);
  const bases = prob.base.map((bc) => `P(${bc.n}) says “${tidy(bc.inst)}”${bc.simp && tidy(bc.simp) !== tidy(bc.inst) ? `, i.e. “${tidy(bc.simp)}”` : ''}, which is true.`);
  L.push('(B) ' + bases.join(' '));
  const kmin = prob.n0 + (prob.nb || 1) - 1;
  if (prob.strong) {
    const list = prob.nb > 1 ? `P(${prob.n0}), P(${prob.n0 + 1}), …, P(k)` : `P(${prob.n0}), …, P(k)`;
    L.push(`(R) Suppose k ≥ ${kmin} is such that ${list} are all true. We show P(k + 1) is true, i.e. ${prob.P.k1}.`);
  } else {
    L.push(`(R) Suppose P(k) is true for some k ≥ ${prob.n0}, i.e. ${prob.P.k}. We show P(k + 1) is true, i.e. ${prob.P.k1}.`);
  }
  const lines = [`${prob.lhsShow ?? showE(prob.lhs1)}`];
  for (const c of prob.chain) {
    const why = c.note ? `  (${c.note})` : c.why === 'ih' ? '  (by P(k))' : c.why === 'ihs' ? '  (by P(k) and P(k − 1))' : c.why === 'rec' ? '  (by the recurrence)' : c.why === 'split' ? '' : '';
    lines.push(`   ${c.rel} ${c.show ?? showE(c.e)}${why}`);
  }
  L.push(...lines);
  if (prob.kind === 'div') L.push(`which is divisible by ${prob.div.d} since ${tidy(prob.cofactor)} is an integer. So P(k + 1) is true.`);
  else if (prob.kind === 'parity') L.push(`which is ${prob.parity.odd ? 'odd' : 'even'}, since ${showE(subst(prob.parity.expr, 'k'))} is ${prob.parity.odd ? 'odd' : 'even'} by P(k) and the other term is even. So P(k + 1) is true.`);
  else L.push('So P(k + 1) is true.');
  L.push(`Hence by ${strongName}${prob.strong ? ' (the second principle of induction)' : ''}, P(n) is true for all n ≥ ${prob.n0}. □`);
  return L;
}
const tidy = (s) => s.replace(/sqrt\(2\)\^/g, '(√2)^').replace(/sqrt\(2\)/g, '√2').replace(/\^(\d)/g, (m, d) => '⁰¹²³⁴⁵⁶⁷⁸⁹'[d]).replace(/a_(\d)/g, (m, d) => 'a' + '₀₁₂₃₄₅₆₇₈₉'[d]).replace(/ - /g, ' − ').replace(/\*/g, '×');
export const subst = (e, by) => e.replace(/n/g, by);
export function showE(e) { try { return A.pretty(A.parseExpr(e)); } catch { return e; } }
