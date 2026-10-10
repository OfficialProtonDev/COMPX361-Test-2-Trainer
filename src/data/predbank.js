// Scenarios and sentence banks for predicate-logic translation drills.
// Two-sorted scenarios follow the past papers: x ranges over X, y over Y, P(x, y).

export const SCENARIOS = {
  dogs: {
    id: 'dogs', title: 'Dogs and cats (2025 Test 2)',
    setup: 'Let X be the set of all dogs and Y the set of all cats. P(x, y) = “dog x chases cat y”.',
    sig: { sorts: ['X', 'Y'], preds: { P: ['X', 'Y'] }, domAlias: { X: 'X', Y: 'Y' }, sortName: { X: 'dog', Y: 'cat' }, sortPlural: { X: 'dogs', Y: 'cats' } },
    sorts: { X: { sing: 'dog', plural: 'dogs', label: 'd' }, Y: { sing: 'cat', plural: 'cats', label: 'c' } },
    preds: { P: { args: ['X', 'Y'], verb: 'chases', verbNone: 'chases no cats' } },
  },
  music: {
    id: 'music', title: 'People and instruments (2023 Test 2)',
    setup: 'Let X be the set of all people and Y the set of all musical instruments. P(x, y) = “person x can play musical instrument y”.',
    sig: { sorts: ['X', 'Y'], preds: { P: ['X', 'Y'] }, domAlias: { X: 'X', Y: 'Y' }, sortName: { X: 'person', Y: 'instrument' }, sortPlural: { X: 'people', Y: 'instruments' } },
    sorts: { X: { sing: 'person', plural: 'people', label: 'p' }, Y: { sing: 'instrument', plural: 'instruments', label: 'i' } },
    preds: { P: { args: ['X', 'Y'], verb: 'can play', verbNone: 'can play no instruments' } },
  },
  cars: {
    id: 'cars', title: 'People and cars (lecture notes)',
    setup: 'Let X be the people living on a street and Y the cars on that street. P(x, y) = “person x has driven car y”.',
    sig: { sorts: ['X', 'Y'], preds: { P: ['X', 'Y'] }, domAlias: { X: 'X', Y: 'Y' }, sortName: { X: 'person', Y: 'car' }, sortPlural: { X: 'people', Y: 'cars' } },
    sorts: { X: { sing: 'person', plural: 'people', label: 'p' }, Y: { sing: 'car', plural: 'cars', label: 'c' } },
    preds: { P: { args: ['X', 'Y'], verb: 'has driven', verbNone: 'has driven no cars' } },
  },
  papers: {
    id: 'papers', title: 'Students and papers',
    setup: 'Let X be the set of students in the class and Y the set of COMPX papers. P(x, y) = “student x has passed paper y”.',
    sig: { sorts: ['X', 'Y'], preds: { P: ['X', 'Y'] }, domAlias: { X: 'X', Y: 'Y' }, sortName: { X: 'student', Y: 'paper' }, sortPlural: { X: 'students', Y: 'papers' } },
    sorts: { X: { sing: 'student', plural: 'students', label: 's' }, Y: { sing: 'paper', plural: 'papers', label: 'p' } },
    preds: { P: { args: ['X', 'Y'], verb: 'has passed', verbNone: 'has passed no papers' } },
  },
  friends: {
    id: 'friends', title: 'Friends (tutorial 8)',
    setup: 'P(x, y) is the predicate “x is a friend of y”, defined on the set of all people.',
    sig: { sorts: ['D'], preds: { P: ['D', 'D'] }, domAlias: {}, sortName: { D: 'person' }, sortPlural: { D: 'people' } },
    sorts: { D: { sing: 'person', plural: 'people', label: 'p' } },
    preds: { P: { args: ['D', 'D'], verb: 'is a friend of', verbNone: 'is a friend of nobody' } },
  },
  crows: {
    id: 'crows', title: 'Crows (tutorial 8)',
    setup: 'P(x) is “x is a crow” and Q(x) is “x is black”, where x ranges over all animals.',
    sig: { sorts: ['D'], preds: { P: ['D'], Q: ['D'] }, domAlias: {}, sortName: { D: 'animal' }, sortPlural: { D: 'animals' } },
    sorts: { D: { sing: 'animal', plural: 'animals', label: 'a' } },
    preds: { P: { args: ['D'], is1: 'is a crow', isN: 'are crows' }, Q: { args: ['D'], is1: 'is black', isN: 'are black' } },
  },
};

// Two-sorted templates. Each English list follows the scenario order: dogs, music, cars, papers.
const TWO = [
  { id: 'AE', f: '∀x ∃y : P(x, y)', lvl: 1, en: {
    dogs: 'Every dog chases at least one cat.', music: 'Everyone can play some instrument.',
    cars: 'Everybody has driven a car.', papers: 'Every student has passed at least one paper.' } },
  { id: 'AE2', f: '∀y ∃x : P(x, y)', lvl: 1, en: {
    dogs: 'Every cat is chased by some dog.', music: 'Every musical instrument can be played by someone.',
    cars: 'Every car has been driven by somebody.', papers: 'Every paper has been passed by some student.' } },
  { id: 'EA', f: '∃x ∀y : P(x, y)', lvl: 1, en: {
    dogs: 'Some dog chases every cat.', music: 'Someone can play every instrument.',
    cars: 'Someone has driven every car.', papers: 'Some student has passed every paper.' } },
  { id: 'EA2', f: '∃y ∀x : P(x, y)', lvl: 1, en: {
    dogs: 'There is a cat that every dog chases.', music: 'There is an instrument everyone can play.',
    cars: 'Some car has been driven by everybody.', papers: 'There is a paper every student has passed.' } },
  { id: 'nEA', f: '¬∃x ∀y : P(x, y)', lvl: 2, en: {
    dogs: 'No dog chases every cat.', music: 'Nobody can play every instrument.',
    cars: 'Nobody has driven every car.', papers: 'No student has passed every paper.' } },
  { id: 'EnE', f: '∃x ¬∃y : P(x, y)', lvl: 2, en: {
    dogs: 'There is a dog that chases no cats.', music: 'Someone can’t play any instrument.',
    cars: 'Someone has never driven any of the cars.', papers: 'There is a student who has passed no papers.' } },
  { id: 'EnE2', f: '∃y ¬∃x : P(x, y)', lvl: 2, en: {
    dogs: 'There is a cat that no dog chases.', music: 'There is an instrument nobody can play.',
    cars: 'There is a car nobody has driven.', papers: 'There is a paper no student has passed.' } },
  { id: 'AA', f: '∀x ∀y : P(x, y)', lvl: 1, en: {
    dogs: 'Every dog chases every cat.', music: 'Everyone can play every instrument.',
    cars: 'Everybody has driven every car.', papers: 'Every student has passed every paper.' } },
  { id: 'nEE', f: '¬∃x ∃y : P(x, y)', lvl: 2, en: {
    dogs: 'No dog chases any cat.', music: 'Nobody can play any instrument.',
    cars: 'Nobody has driven any of the cars.', papers: 'No student has passed any paper.' } },
  { id: 'two', f: '∃x ∃y ∃z : P(x, y) ∧ P(x, z) ∧ (y ≠ z)', lvl: 3, en: {
    dogs: 'Some dog chases more than one cat.', music: 'Some people can play more than one musical instrument.',
    cars: 'Somebody has driven at least two different cars.', papers: 'Some student has passed at least two different papers.' } },
  { id: 'two2', f: '∃y ∃x ∃w : P(x, y) ∧ P(w, y) ∧ (x ≠ w)', lvl: 3, en: {
    dogs: 'Some cat is chased by at least two different dogs.', music: 'Some instrument can be played by at least two different people.',
    cars: 'Some car has been driven by at least two different people.', papers: 'Some paper has been passed by at least two different students.' } },
  { id: 'nAE2', f: '¬∀y ∃x : P(x, y)', lvl: 2, en: {
    dogs: 'Not every cat is chased by some dog.', music: 'Not every instrument can be played by someone.',
    cars: 'Not every car has been driven by somebody.', papers: 'Not every paper has been passed by some student.' } },
  { id: 'most1', f: '∀x ∀y ∀z : (P(x, y) ∧ P(x, z)) → (y = z)', lvl: 3, en: {
    dogs: 'Every dog chases at most one cat.', music: 'Nobody can play more than one instrument.',
    cars: 'Nobody has driven more than one car.', papers: 'Every student has passed at most one paper.' } },
  { id: 'exactly1', f: '∃x ∃y : P(x, y) ∧ ∀z : (P(x, z) → (z = y))', lvl: 3, en: {
    dogs: 'Some dog chases exactly one cat.', music: 'Someone can play exactly one instrument.',
    cars: 'Somebody has driven exactly one car.', papers: 'Some student has passed exactly one paper.' } },
  { id: 'AnA', f: '∀x ∃y : ¬P(x, y)', lvl: 2, en: {
    dogs: 'Every dog fails to chase at least one cat.', music: 'Everyone has some instrument they can’t play.',
    cars: 'Everybody has some car they haven’t driven.', papers: 'Every student has some paper they haven’t passed.' } },
];

const ONE = {
  friends: [
    { id: 'F1', f: '∃x ∀y : P(x, y)', lvl: 1, en: 'Someone is a friend of everyone.' },
    { id: 'F2', f: '∃x ∃y ∃z : P(x, y) ∧ P(x, z) ∧ (y ≠ z)', lvl: 3, en: 'Someone is a friend of at least two different people.' },
    { id: 'F3', f: '∀x ∀y : P(x, y) → P(y, x)', lvl: 2, en: 'For any two people x, y, if x is a friend of y, then y is a friend of x.' },
    { id: 'F4', f: '¬∃y ¬∃x : P(x, y)', lvl: 2, en: 'There is nobody with no friends.' },
    { id: 'F5', f: '∀x ∃y : P(x, y)', lvl: 1, en: 'Everyone is a friend of somebody.' },
    { id: 'F6', f: '∃x ¬∃y : P(x, y)', lvl: 2, en: 'Someone is a friend of nobody.' },
    { id: 'F7', f: '∀x : ¬P(x, x)', lvl: 2, en: 'Nobody is a friend of themselves.' },
    { id: 'F8', f: '∃y ∀x : ¬P(x, y)', lvl: 2, en: 'Somebody has no friends.' },
  ],
  crows: [
    { id: 'C1', f: '∀x : P(x) → Q(x)', lvl: 1, en: 'All crows are black.' },
    { id: 'C2', f: '∃x : ¬P(x) ∧ ¬Q(x)', lvl: 1, en: 'There are animals that are neither crows nor black.' },
    { id: 'C3', f: '∃x : P(x) ∧ Q(x)', lvl: 1, en: 'There is a black crow.' },
    { id: 'C4', f: '∃x : ¬P(x) ∧ Q(x)', lvl: 2, en: 'Not all black animals are crows.' },
    { id: 'C6', f: '∀x : Q(x) → P(x)', lvl: 2, en: 'Only crows are black.' },
    { id: 'C7', f: '∃x : P(x) ∧ ¬Q(x)', lvl: 2, en: 'Not all crows are black.' },
    { id: 'C8', f: '∀x : P(x) → ¬Q(x)', lvl: 2, en: 'No crow is black.' },
  ],
};

export function sentences(scenId) {
  if (ONE[scenId]) return ONE[scenId].map((s) => ({ ...s, scen: scenId }));
  return TWO.map((t) => ({ id: t.id, f: t.f, lvl: t.lvl, en: t.en[scenId], scen: scenId }));
}

export const SCENARIO_IDS = ['dogs', 'music', 'cars', 'papers', 'friends', 'crows'];

// Truth of quantified statements about number systems (ℕ = {1, 2, 3, …} in this course).
export const NUMBER_FACTS = [
  { f: '∀x ∈ ℝ ∃y ∈ ℝ : x + y = 0', truth: true, why: 'True: for any x, let y = −x.', src: 'Tutorial 8 Q3(a)' },
  { f: '∃y ∈ ℝ ∀x ∈ ℝ : x + y = 0', truth: false, why: 'False: whatever y is, x = 1 − y gives x + y = 1 ≠ 0.', src: 'Tutorial 8 Q3(b)' },
  { f: '∃y ∈ ℝ ∀x ∈ ℝ : xy = 0', truth: true, why: 'True: y = 0 gives xy = 0 for every x.', src: 'Tutorial 8 Q3(c)' },
  { f: '∀x ∈ ℝ ∀y ∈ ℝ ∀z ∈ ℝ : (x ≠ 0) ∧ (xy = xz) → (y = z)', truth: true, why: 'True: if x ≠ 0 and xy = xz, divide both sides by x to get y = z.', src: 'Tutorial 8 Q3(d)' },
  { f: '∀x ∈ ℝ ∃n ∈ ℕ : |n − x| < 0.2', truth: false, why: 'False: no natural number is within 0.2 of x = 1.5.', src: 'PRED2 notes' },
  { f: '∀n ∈ ℕ ∃x ∈ ℝ : |n − x| < 0.2', truth: true, why: 'True: just take x = n.', src: 'PRED2 notes' },
  { f: '∃x ∈ ℝ ∃y ∈ ℝ : x² + y² = 0', truth: true, why: 'True: x = y = 0.', src: 'PRED2 notes' },
  { f: '∀x ∈ ℝ ¬∃y ∈ ℕ : xy = 1', truth: false, why: 'False: it says ∀x ∀y : xy ≠ 1, but x = y = 1 gives xy = 1.', src: 'PRED2 notes' },
  { f: '∀x ∈ ℕ ∃y ∈ ℝ : y² = x', truth: true, why: 'True: every positive integer has a real square root.', src: 'PRED2 notes' },
  { f: '¬∃x ∈ ℕ ¬∃y ∈ ℕ : ¬(x ≤ y)', truth: false, why: 'False: it is equivalent to ¬∃x ∈ ℕ ∀y ∈ ℕ : x ≤ y, but x = 1 is ≤ every natural number.', src: 'PRED2 notes' },
  { f: '∀x ∈ ℝ : x² ≥ 2x + 1', truth: false, why: 'False: x = 0 is a counterexample (0 ≥ 1 fails).', src: 'PRED1 notes' },
  { f: '∃x ∈ ℝ : x² ≥ 2x + 1', truth: true, why: 'True: x = 4 works (16 ≥ 9).', src: 'PRED1 notes' },
  { f: '∃x ∈ ℝ : x² + 1 = 0', truth: false, why: 'False: no real x has x² = −1. (Over ℂ it would be true: x = i.)', src: 'PRED1 notes' },
  { f: '∀x ∈ ℕ ∃y ∈ ℕ : y < x', truth: false, why: 'False: x = 1 is a counterexample, because ℕ starts at 1 in this course.', src: 'new' },
  { f: '∃x ∈ ℕ ∀y ∈ ℕ : x ≤ y', truth: true, why: 'True: x = 1.', src: 'new' },
  { f: '∀x ∈ ℝ ∃y ∈ ℝ : y > x', truth: true, why: 'True: take y = x + 1.', src: 'new' },
  { f: '∃y ∈ ℝ ∀x ∈ ℝ : y > x', truth: false, why: 'False: there is no largest real number; x = y + 1 beats any y.', src: 'new' },
  { f: '∃m ∈ ℕ ∃n ∈ ℕ : m + n = 1', truth: false, why: 'False: the smallest possible sum is 1 + 1 = 2, since ℕ starts at 1.', src: 'new' },
  { f: '∀m ∈ ℕ ∃n ∈ ℕ : m + n = 5', truth: false, why: 'False: m = 5 (or anything ≥ 5) has no partner n ∈ ℕ.', src: 'based on PRED2' },
  { f: '∃m ∈ ℕ ∃n ∈ ℕ : m + n = 5', truth: true, why: 'True: the truth set {(1,4), (2,3), (3,2), (4,1)} is non-empty.', src: 'PRED2 notes' },
  { f: '∀x ∈ ℝ : (x² = 0) → (x = 0)', truth: true, why: 'True: the only real number whose square is 0 is 0.', src: 'PRED1 notes' },
  { f: '∀n ∈ ℕ : n² ≥ n', truth: true, why: 'True: n ≥ 1, so n² = n·n ≥ n·1 = n.', src: 'new' },
];
