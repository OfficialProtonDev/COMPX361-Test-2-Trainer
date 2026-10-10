import { useState } from 'preact/hooks';
import { MathText, Seg, Chip } from '../kit.jsx';
import { LawSheet } from '../drills/prop.jsx';
import { CodeTable } from '../drills/tm.jsx';
import { THEORY, HALTING_PROOF } from '../../data/theory.js';
import * as P from '../../engines/prop.js';

const TABS = [
  { value: 'supplied', label: 'Supplied in the test' },
  { value: 'tm', label: 'Turing machines' },
  { value: 'gram', label: 'Grammars' },
  { value: 'prop', label: 'Propositional' },
  { value: 'pred', label: 'Predicate' },
  { value: 'ind', label: 'Induction' },
];

function Block({ title, children }) {
  return <section class="card stack"><h2 class="h2">{title}</h2>{children}</section>;
}
const L = ({ t }) => <div class="model-line" style={{ fontFamily: 'var(--font-math)', fontSize: '17px' }}><MathText text={t} /></div>;

export function ReferencePage() {
  const [tab, setTab] = useState('supplied');
  const conn = ['¬', '∧', '∨', '⊕', '→', '↔'];
  return (
    <div class="sheet">
      <header class="stack-sm">
        <div class="h-kicker">Reference</div>
        <h1 class="h-title">Reference sheets</h1>
        <p class="h-sub">The two sheets you are given in the test, plus a one-page summary of each topic in the lecturer’s notation.</p>
        <div class="row" style={{ marginTop: '6px' }}><Seg value={tab} onChange={setTab} label="Section" options={TABS} /></div>
      </header>

      {tab === 'supplied' && (
        <>
          <Block title="Code table for Turing numbers (TM3)"><CodeTable /><p class="small muted">Digits i = 0…9 are coded as the binary for 16 + i; every code starts with 1.</p></Block>
          <Block title="Laws of logical equivalence"><LawSheet /><p class="small muted">Law 13 (rule for NAND) was printed on the 2025 sheet but not on 2023 or 2024. Quote the law on every line of a proof.</p></Block>
        </>
      )}

      {tab === 'tm' && (
        <>
          <Block title="Normalised TMs and Turing numbers">
            <ul class="prose">
              <li>An NTM has states 0, 1, …, N: 0 is the start state, N the halt state.</li>
              <li>List form: N, then for each state 0 … N − 1 the instructions for reading 0, 1, b, separated by “/”. Each instruction is ⊥ (undefined) or “state, action”, where the action writes 0, 1, b or moves L, R.</li>
              <li>Example (TM3): 19/⊥/1, 0/⊥/2, R/⊥/⊥/⊥/3, b/5, L/…  → 10001 11001 11111 11011 11111 …</li>
              <li>Invalid codes: wrong number of instructions (must be exactly 3N), a state above N referenced, or a malformed instruction (tutorial 5 Q1(d)).</li>
              <li>The smallest NTM: N = 0, a single state that is both start and halt. Code “0” = 10000 = 16. It computes the identity function.</li>
            </ul>
          </Block>
          {THEORY.filter((t) => ['utm', 'halting', 'undecidable', 'church'].includes(t.id)).map((t) => (
            <Block key={t.id} title={`${t.title} (model answer)`}>{t.model.split('\n').map((l, i) => <p key={i}>{l}</p>)}<div><Chip kind="src">{t.src}</Chip></div></Block>
          ))}
          <Block title="Why the halting problem can’t be solved (TM4 outline)"><ol class="prose">{HALTING_PROOF.map((l, i) => <li key={i}><MathText text={l} /></li>)}</ol></Block>
        </>
      )}

      {tab === 'gram' && (
        <>
          <Block title="Grammar types (exact course definitions)">
            <table class="plain"><thead><tr><th>Type</th><th>Every production is…</th></tr></thead><tbody>
              <tr><td>Regular (type 3)</td><td><MathText text="A ⇒ aB,  A ⇒ a,  or S ⇒ λ   (a a single terminal)" /></td></tr>
              <tr><td>Context-free (type 2)</td><td><MathText text="A ⇒ α with α ≠ λ, or S ⇒ λ" /></td></tr>
              <tr><td>Context-sensitive (type 1)</td><td><MathText text="βAγ ⇒ βαγ with α ≠ λ, or S ⇒ λ" /></td></tr>
              <tr><td>Arbitrary (type 0)</td><td><MathText text="r ⇒ w, where r contains at least one variable" /></td></tr>
            </tbody></table>
            <p class="small muted">Only the start symbol may go to λ in types 1–3. A non-regular grammar can still generate a regular language (GRAM2).</p>
          </Block>
          <Block title="Regular grammar ↔ automaton (GRAM2)">
            <ul class="prose">
              <li>Grammar → NFSA: states <MathText text="V ∪ {Q_f}" />, start S, accepting state <MathText text="Q_f" />. <MathText text="A ⇒ aB" /> gives an edge <MathText text="A —a→ B" />; <MathText text="A ⇒ a" /> gives <MathText text="A —a→ Q_f" />; <MathText text="S ⇒ λ" /> gives <MathText text="S —λ→ Q_f" />.</li>
              <li>DFSA → grammar: V = Q, <MathText text="S = q0" />, T = X. An edge <MathText text="A —a→ B" /> gives <MathText text="A ⇒ aB" />, plus <MathText text="A ⇒ a" /> if B is accepting; if λ ∈ L(M) (q₀ is accepting) add <MathText text="S ⇒ λ" />.</li>
              <li>Regular expression → grammar: get a DFSA first (no λ-edges), then use the rule above (tutorial 6 Q4).</li>
            </ul>
          </Block>
          <Block title="The Chomsky hierarchy (GRAM4)">
            <L t="regular ⊂ context-free ⊂ context-sensitive ⊂ arbitrary (grammars)" />
            <L t="regular ⊂ context-free ⊂ context-sensitive ⊂ recursively enumerable (languages)" />
            <table class="plain"><thead><tr><th>Grammar</th><th>Automaton</th></tr></thead><tbody>
              <tr><td>Regular</td><td>DFSA</td></tr><tr><td>Context-free</td><td>Pushdown automaton</td></tr><tr><td>Context-sensitive</td><td>Linear bounded automaton</td></tr><tr><td>Arbitrary</td><td>Turing machine (semidecides only)</td></tr>
            </tbody></table>
            <ul class="prose small">
              <li>Context-sensitive languages are recursive (decidable membership); some recursive languages are not context-sensitive; some r.e. languages are not recursive; some languages aren’t r.e. at all.</li>
              <li>Undecidable for context-free grammars: does G generate every string? Is L(G₁) = L(G₂)? L(G₁) ⊆ L(G₂)? L(G₁) ∩ L(G₂) = ∅?</li>
              <li>{'{aⁿbⁿcⁿ}'} is context-sensitive but not context-free; {'{0ⁿ1ⁿ}'} is context-free but not regular.</li>
            </ul>
          </Block>
        </>
      )}

      {tab === 'prop' && (
        <>
          <Block title="Connectives">
            <div class="scroll-x"><table class="tt"><thead><tr><th><i>p</i></th><th><i>q</i></th>{['p ∧ q', 'p ∨ q', 'p → q', 'p ↔ q', 'p ⊕ q', 'p ↑ q', 'p ↓ q'].map((c) => <th key={c}><MathText text={c} /></th>)}</tr></thead>
              <tbody>{P.rows(['p', 'q']).map((env, i) => <tr key={i}><td class="var">{env.p ? 'T' : 'F'}</td><td class="var">{env.q ? 'T' : 'F'}</td>{['p ∧ q', 'p ∨ q', 'p → q', 'p ↔ q', 'p ⊕ q', 'p ↑ q', 'p ↓ q'].map((c) => <td key={c}>{P.evaluate(P.parse(c), env) ? 'T' : 'F'}</td>)}</tr>)}</tbody></table></div>
            <p class="small muted">Binding priority (highest first, PROP2): <MathText text={conn.join(', ')} />. A repeated connective binds to the left. ↑ and ↓ aren’t in the list, so bracket them.</p>
          </Block>
          <Block title="Status, equivalence, consequence (PROP2–PROP4)">
            <ul class="prose">
              <li>Valid (tautology): T for every valuation. Satisfiable: T for at least one (a model). Unsatisfiable (contradiction): no models. A counterexample is a valuation making it F.</li>
              <li>P ⇔ Q (logically equivalent) exactly when P ↔ Q is valid. P ⇒ Q (Q is a logical consequence of P) exactly when P → Q is valid.</li>
              <li>An argument with premises P₁, …, Pₙ and conclusion C is valid exactly when (P₁ ∧ ⋯ ∧ Pₙ) → C is a tautology. Show it by a truth table, or try to make it false (all premises T, conclusion F) and reach a contradiction.</li>
              <li>Truth-table rows go in the course order: FF, FT, TF, TT; with three variables FFF, FFT, FTF, TFF, FTT, TFT, TTF, TTT.</li>
            </ul>
          </Block>
          <Block title="Functional completeness (PROP5)">
            <ul class="prose">
              <li>A set of connectives is functionally complete if every truth table is the truth table of some WFF using only those connectives.</li>
              <li>Full DNF: one conjunction per T row, joined by ∨. So {'{¬, ∧, ∨}'} is complete, hence {'{¬, ∧}'} and {'{¬, ∨}'} (De Morgan), {'{F, →}'}, {'{↑}'} and {'{↓}'}.</li>
            </ul>
            {['¬A ⇔ A ↑ A', 'A ∧ B ⇔ (A ↑ B) ↑ (A ↑ B)', 'A ∨ B ⇔ (A ↑ A) ↑ (B ↑ B)', '¬A ⇔ A → F', 'A ∨ B ⇔ ¬A → B'].map((t) => <L key={t} t={t} />)}
          </Block>
        </>
      )}

      {tab === 'pred' && (
        <>
          <Block title="Quantifiers (PRED1, PRED2)">
            <ul class="prose">
              <li>∀x ∈ U : P(x) is true iff the truth set of P is all of U; ∃x ∈ U : P(x) iff the truth set is non-empty. Over a finite U, ∀ is a big ∧ and ∃ a big ∨.</li>
              <li>To prove ∃: give an example. To disprove ∀: give a counterexample. ℕ = {'{1, 2, 3, …}'} in this course.</li>
              <li>Order matters: ∀x ∃y : P(x, y) (everyone has driven some car) differs from ∃y ∀x : P(x, y) (some car has been driven by everyone). Two ∀s (or two ∃s) can be swapped.</li>
              <li>A variable is bound by a quantifier, otherwise free. A predicate becomes a proposition once every variable is bound.</li>
            </ul>
            {['¬∀x : P(x)  ⇔  ∃x : ¬P(x)', '¬∃x : P(x)  ⇔  ∀x : ¬P(x)', '∃x ¬∃y ∀z : ¬Q(x, y, z)  ⇔  ∃x ∀y ∃z : Q(x, y, z)'].map((t) => <L key={t} t={t} />)}
          </Block>
          <Block title="Translation patterns">
            <table class="plain"><tbody>
              {[['All A are B', '∀x : A(x) → B(x)'], ['Some A are B', '∃x : A(x) ∧ B(x)'], ['No A is B', '¬∃x : A(x) ∧ B(x)'], ['Not all A are B', '∃x : A(x) ∧ ¬B(x)'], ['Every dog chases at least one cat', '∀x ∃y : P(x, y)'], ['No dog chases every cat', '¬∃x ∀y : P(x, y)'], ['There is a dog that chases no cats', '∃x ¬∃y : P(x, y)'], ['Some people can play more than one instrument', '∃x ∃y ∃z : P(x, y) ∧ P(x, z) ∧ (y ≠ z)']].map(([a, b]) => <tr key={a}><td>{a}</td><td><MathText text={b} /></td></tr>)}
            </tbody></table>
          </Block>
        </>
      )}

      {tab === 'ind' && (
        <>
          <Block title="Ordinary induction: the lecturer’s layout">
            {['For n ≥ n₀, let P(n) be the predicate that “…”.   [½]', '(B) P(n₀) says “…”, i.e. “…”, which is true.   [½]', '(R) Suppose P(k) is true for some k ≥ n₀, i.e. … .   [½]', 'We show P(k + 1) is true, i.e. … .', 'LHS = … = … (by P(k)) = … = RHS.   [3]', 'So P(k + 1) is true. Hence by induction, P(n) is true for all n ≥ n₀. □   [½]'].map((t) => <L key={t} t={t} />)}
            <p class="small muted">Marks as circled on the official 2023 solutions (Q9, 5 marks per part); the 2024 and 2025 solutions don’t give a split. IND notes: “Your answers to induction problems will get around half marks if you get all the steps right except the recursive steps.”</p>
          </Block>
          <Block title="Strong induction (second principle)">
            {['(B) Check P(n₀), P(n₀ + 1), …, P(n₀ + m − 1).', '(R) Suppose k ≥ n₀ + m − 1 is such that P(n₀), …, P(k) are all true. We show P(k + 1).', 'Hence by strong induction, P(n) is true for all n ≥ n₀. □'].map((t) => <L key={t} t={t} />)}
            <ul class="prose small">
              <li>Recurrences: one base case for each initial value given in the definition (IND3). With a₁ and a₂ given, check P(1) and P(2), then run (R) for k ≥ 2; tutorial 9 Q4 gives a₀, a₁, a₂, so the official solution checks three base cases.</li>
              <li>Stamps a &lt; b: base cases n₀, …, n₀ + a − 1; in (R) use P(k + 1 − a): k + 1 = (k + 1 − a) + a.</li>
              <li>The number of base cases is whatever makes (R) work for every k in range (IND2).</li>
            </ul>
          </Block>
          <Block title="Common ways to lose marks">
            <ul class="prose">
              <li>No “let P(n) be the predicate that …”, or no domain (n ≥ ?).</li>
              <li>Base case not checked, or checked at the wrong n (“n &gt; 1” means start at 2).</li>
              <li>Writing P(k + 1) without brackets: (k + 1)² is not k² + 1.</li>
              <li>Using P(k + 1) to prove P(k + 1), or never visibly using P(k).</li>
              <li>A step that only works for large k, without enough base cases (IND2, tutorial 9 Q5).</li>
            </ul>
          </Block>
        </>
      )}
    </div>
  );
}
