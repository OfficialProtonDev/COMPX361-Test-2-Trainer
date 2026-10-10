// Written-answer questions with the lecturer's model answers. The mark splits are the trainer's
// suggestion (the official 2024/2025 solutions give no breakdown).
export const THEORY = [
  {
    id: 'halting', title: 'The Halting Problem', marks: 4, src: '2023 Test 2 Q1 · 2025 Test 2 Q2',
    q: 'Briefly explain what the Halting problem is, whether it has a solution, and its significance in the theory of computation.',
    model: 'The Halting problem is whether or not there is a Turing machine (or algorithm!) that can take as input the Turing number of a normalised Turing machine N and an input to it, and determine whether or not N completes a computation on that input.\nThere is no such Turing machine (it is undecidable).\nThis means some problems cannot be solved using Turing machines / algorithms.',
    scheme: [
      { p: 'What it asks: a TM/algorithm that takes (the Turing number of) any NTM N together with an input to it', m: 1 },
      { p: '…and decides whether N completes a computation on that input', m: 1 },
      { p: 'No such TM exists: the problem is undecidable', m: 1 },
      { p: 'Significance: some problems cannot be solved by any algorithm / TM', m: 1 },
    ],
    notes: 'The official answer is three sentences long; full marks do not need the proof. The official answers and the TM4 notes say “completes a computation” (TM4: failing to halt is only one way a computation can fail to complete). Do not deduct for “halts”, but say in the feedback that the course’s wording is “completes a computation”.',
  },
  {
    id: 'utm', title: 'Universal Turing machines', marks: 3, src: '2024 Test 2 Q2',
    q: 'Briefly explain what a universal Turing machine is, whether they exist, and their significance in the theory of computation.',
    model: 'A universal Turing machine can take as input any NTM (expressed as its Turing number, for example), together with an input to it, and give exactly the same output as the NTM would have with that input (including not completing if that would have occurred).\nThey do exist.\nThey model computers, which take as inputs programs together with inputs to those programs.',
    scheme: [
      { p: 'Takes (the Turing number of) any NTM plus an input to it, and gives exactly the output that NTM would give (including not completing)', m: 1.5 },
      { p: 'They exist', m: 0.5 },
      { p: 'Significance: it models a computer running a program on an input', m: 1 },
    ],
  },
  {
    id: 'undecidable', title: 'Undecidable problems', marks: 2, src: '2025 Test 2 Q5 · 2024 Test 2 Q5',
    q: 'Give two examples of undecidable problems.',
    model: 'The Halting problem.\nFrom the theory of grammars: whether two context-free grammars generate the same language (or whether L(G₁) ⊆ L(G₂), whether L(G₁) ∩ L(G₂) = ∅, or whether a CFG generates all possible strings).\nAnother: whether a WFF of predicate logic is a tautology (valid).',
    scheme: [
      { p: 'First correct example of an undecidable problem', m: 1 },
      { p: 'Second, different correct example', m: 1 },
    ],
    notes: 'Accept any problems the course calls undecidable: the halting problem; for CFGs: L(G₁) = L(G₂), L(G₁) ⊆ L(G₂), L(G₁) ∩ L(G₂) = ∅, whether G generates every string; validity of predicate-logic WFFs; whether a finite set of matrices multiplies to zero in some order. Do not accept decidable ones (e.g. membership of a regular language, tautology-hood in propositional logic).',
  },
  {
    id: 'fc', title: 'Functional completeness', marks: 1, src: '2024 Test 2 Q7(a)',
    q: 'In propositional logic, what does it mean to say that a set of connectives is functionally complete?',
    model: 'For any hypothetical truth table, there is a WFF involving only the given set of connectives that has that truth table. Equivalently, given any WFF involving any connectives, there is a logically equivalent one using only the given connectives.',
    scheme: [{ p: 'Every truth table (every Boolean function) is the truth table of some WFF using only those connectives', m: 1 }],
  },
  {
    id: 'church', title: 'Undecidable means…', marks: 2, src: 'TM4 notes',
    q: 'What does it mean for a problem to be undecidable? Does it mean we can never answer the question for a particular case?',
    model: 'A problem is undecidable if there is no Turing machine (no algorithm) that answers it correctly for every instance.\nIt does not mean we can never answer it in a particular case: e.g. some TMs obviously complete a computation on every input. There is just no single method that works in all cases (and so no finite set of methods either).',
    scheme: [
      { p: 'No single TM/algorithm answers every instance', m: 1 },
      { p: 'Particular instances can still be answerable', m: 1 },
    ],
  },
];

export const HALTING_PROOF = [
  'Suppose some NTM H decides, for each n (in unary), whether M[n] completes a computation on input n, outputting 11 for “yes” and 1 for “no”. H always completes; its halt state is N.',
  'Build H′ from H: make N an ordinary state, add N+1, N+2, N+3 with N+3 the new halt state, and edges N —1/R→ N+1, N+1 —1/1→ N+2, N+1 —b/L→ N+3.',
  'H′ is an NTM, so H′ = M[p] for some index p. Run it on input p.',
  'If M[p] fails to complete on p, H ends in (λ, N, 1); then H′ goes (λ, N, 1) ⊢ (1, N+1, λ) ⊢ (λ, N+3, 1): it completes. Contradiction.',
  'If M[p] completes on p, H ends in (λ, N, 11); then H′ goes (λ, N, 11) ⊢ (1, N+1, 1) ⊢ (1, N+2, 1) and gets stuck: it does not complete. Contradiction.',
  'Either way we have a contradiction, so no such H exists: the Halting Problem is undecidable.',
];
