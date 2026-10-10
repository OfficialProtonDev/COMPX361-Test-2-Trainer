import { TableDrill, LawsDrill, NandDrill, DnfDrill, ArgueDrill, BindDrill } from './drills/prop.jsx';
import { Reg2NfsaDrill, Fa2RegDrill, DeriveDrill, CsDrill, DesignDrill, ClassifyDrill } from './drills/gram.jsx';
import { TranslateDrill, EnglishDrill, NegateDrill, TruthDrill } from './drills/pred.jsx';
import { ProofDrill, StrongDrill, FlawDrill, WriteDrill } from './drills/ind.jsx';
import { DecodeDrill, EncodeDrill, TheoryDrill, MooreDrill } from './drills/tm.jsx';

import { HomePage } from './pages/home.jsx';
import { PapersPage } from './pages/papers.jsx';
import { MockPage } from './pages/mock.jsx';
import { ReferencePage } from './pages/reference.jsx';

const mk = (id, title, icon, topic, desc, C) => ({ id, title, icon, topic, desc, C });

export const DRILLS = Object.fromEntries([
  mk('tm-decode', 'Decode a Turing number', '⊥', 'Turing machines', 'Bits → symbols → NTM diagram, as in 2024 and 2025 Q1.', DecodeDrill),
  mk('tm-encode', 'Encode an NTM', '/', 'Turing machines', 'State diagram → list form → binary Turing number.', EncodeDrill),
  mk('tm-theory', 'Halting problem & UTMs', '∞', 'Turing machines', 'Explanations marked against model answers from the official solutions, plus quick true/false.', TheoryDrill),
  mk('moore', 'Moore machines', '↻', 'Turing machines', 'Trace outputs and design machines (tutorial 5).', MooreDrill),
  mk('g-reg2nfsa', 'Regular grammar → NFSA', '→', 'Grammars & automata', 'Build the NFSA: one state per variable plus one accepting state.', Reg2NfsaDrill),
  mk('g-fa2reg', 'DFSA → regular grammar', '⇐', 'Grammars & automata', 'Productions from a diagram or δ table, then a derivation.', Fa2RegDrill),
  mk('g-derive', 'Derivations & parse trees', '⇒', 'Grammars & automata', 'Derive a string step by step and draw its parse tree.', DeriveDrill),
  mk('g-cs', 'Non-context-free derivations', '⇄', 'Grammars & automata', 'Productions with more than one symbol on the left, like 0A ⇒ 01 and BA ⇒ AB (tutorial 6 Q2).', CsDrill),
  mk('g-design', 'Design a grammar', '✎', 'Grammars & automata', 'Write a grammar for a language; counterexamples if it’s wrong.', DesignDrill),
  mk('g-classify', 'Grammar types & hierarchy', '⊂', 'Grammars & automata', 'Regular, context-free, context-sensitive, unrestricted.', ClassifyDrill),
  mk('p-table', 'Truth tables & status', 'T', 'Propositional logic', 'Valid, satisfiable, unsatisfiable; equivalence and consequence.', TableDrill),
  mk('p-laws', 'Law-by-law proofs', '⇔', 'Propositional logic', 'Quote a law on every line; each step is checked.', LawsDrill),
  mk('p-nand', 'NAND & other connective sets', '↑', 'Propositional logic', 'Rewrite with ↑ only, ↓ only, {F, →}, {¬, ∧}…', NandDrill),
  mk('p-dnf', 'WFF from a truth table', '∨', 'Propositional logic', 'Full disjunctive normal form.', DnfDrill),
  mk('p-argue', 'Argument validity', '∴', 'Propositional logic', 'English → WFF → tautology or counterexample.', ArgueDrill),
  mk('p-bind', 'Binding priority', '( )', 'Propositional logic', 'Insert brackets, find the main connective.', BindDrill),
  mk('q-translate', 'English → predicate logic', '∀', 'Predicate logic', 'Checked on every small world, with counterexamples.', TranslateDrill),
  mk('q-english', 'Predicate logic → English', '∃', 'Predicate logic', 'Simplify, then say it in plain English.', EnglishDrill),
  mk('q-negate', 'Generalised De Morgan', '¬', 'Predicate logic', 'Push negations through quantifiers, line by line.', NegateDrill),
  mk('q-truth', 'True or false over ℝ and ℕ', 'ℝ', 'Predicate logic', 'Examples and counterexamples (ℕ starts at 1).', TruthDrill),
  mk('i-proof', 'Induction proof builder', 'ℕ', 'Induction', 'Predicate, base case, hypothesis, working, conclusion.', ProofDrill),
  mk('i-strong', 'Strong induction', '⇈', 'Induction', 'Recurrences with two base cases, and stamp problems.', StrongDrill),
  mk('i-flaw', 'Spot the flaw', '?', 'Induction', 'What is wrong with these “proofs”?', FlawDrill),
  mk('i-write', 'Write a full proof', '□', 'Induction', 'Type a whole proof; Claude marks it against a model answer.', WriteDrill),
].map((d) => [d.id, d]));

export const PAGES = {
  home: { id: 'home', title: 'Overview', icon: '◎', C: HomePage },
  papers: { id: 'papers', title: 'Past papers & solutions', icon: '§', C: PapersPage },
  mock: { id: 'mock', title: 'Mock test (60 min)', icon: '⏱', C: MockPage },
  ref: { id: 'ref', title: 'Reference sheets', icon: '≡', C: ReferencePage },
};

export const NAV = [
  { title: 'Start', items: ['home', 'mock', 'papers', 'ref'] },
  { title: 'Turing machines', items: ['tm-decode', 'tm-encode', 'tm-theory', 'moore'] },
  { title: 'Grammars & automata', items: ['g-reg2nfsa', 'g-fa2reg', 'g-derive', 'g-cs', 'g-design', 'g-classify'] },
  { title: 'Propositional logic', items: ['p-table', 'p-laws', 'p-nand', 'p-dnf', 'p-argue', 'p-bind'] },
  { title: 'Predicate logic', items: ['q-translate', 'q-english', 'q-negate', 'q-truth'] },
  { title: 'Induction', items: ['i-proof', 'i-strong', 'i-flaw', 'i-write'] },
];
