-- first-order logic exercises

/-
Consider the "barber paradox," that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves
Prove that this universal statement is a contradiction:
-/
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

theorem barber_paradox : ¬(∀ x : men, shaves barber x ↔ ¬ shaves x x) := by
  intro h
  specialize h barber
  cases h with
  | intro h1 h2 =>
    apply h1
    apply h2
    intro h3
    apply h1
    exact h3
    exact h3
    apply h2
    intro h3
    apply h1
    exact h3
    exact h3

/-
The barber is one who shaves everyone that does not shave oneself.
Please use your proof above to guide your answer to this question: does the barber shave himself?

**TYPE YOUR ANSWER HERE**
 Yes, in the proof we need the barber to shaves himself as the hypothesis so that we can prove that
 all men in the town is shaved.
-/

variable (α : Type) (p : α → Prop)

/-
Prove that a negation of an existential statement is equivalient to a universal statement of the negation.
-/
theorem existential_negation : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  constructor
  --forward
  . intro h
    intro x
    intro hp
    apply h
    exists x

  --backward
  . intro h
    intro ⟨x, hp⟩
    apply h
    exact hp

/-
Prove that if there is an element falsifying a predicate, then not all elements satisfy the predicate.
Note: the converse doesn't hold in constructive logic.
-/
theorem exists_not_not_forall : (∃ x, ¬ p x) → (¬ ∀ x, p x) := by
  intro ⟨x, hp⟩
  intro h
  apply hp
  specialize h x
  exact h
