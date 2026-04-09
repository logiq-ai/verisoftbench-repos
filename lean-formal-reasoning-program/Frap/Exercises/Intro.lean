-- introduction exercises

-- write a proof for each fo the following proposition

theorem curry (p q r : Prop) : (p ∧ q → r) → (p → q → r) := by
  intro h
  intro hp
  intro hq
  apply h
  apply And.intro
  . exact hp
  . exact hq


theorem uncurry (p q r : Prop) : (p → q → r) → (p ∧ q → r) := by
  intro h
  intro hand
  -- Want to proof that r is true then we need to show that "p → q" is true from the hypothesis 'h'
  -- We can proof that "p → q" are true by using the hypothesis 'hand', then we proof that "p ∧ q" is true
  -- Thus, we can apply the hypothesis 'h' to proof that r is true by using the hypotheses 'p' and 'q'
  cases hand with
  | intro hp hq =>
      apply h
      exact hp
      exact hq
