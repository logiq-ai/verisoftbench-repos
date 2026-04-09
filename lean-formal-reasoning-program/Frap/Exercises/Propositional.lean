-- propositional logic exercises

-- write a proof for each fo the following proposition

theorem and_distributes_over_or (p q r : Prop) :
    p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  -- forward
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr with
      | inl hq => apply Or.inl; apply And.intro; exact hp; exact hq
      | inr hr => apply Or.inr; apply And.intro; exact hp; exact hr

  -- backward
  . intro h1
    cases h1 with
    | inl hpq =>
      apply And.intro
      . apply And.left; exact hpq
      . apply Or.inl; apply And.right; exact hpq
    | inr hpr =>
      apply And.intro
      . apply And.left; exact hpr
      . apply Or.inr; apply And.right; exact hpr


theorem or_distributes_over_and_l (p q r : Prop) :
    p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
    apply Iff.intro
    -- forward
    . intro h1
      apply And.intro
      . cases h1 with
        | inl hp => apply Or.inl; exact hp
        | inr hqr => apply Or.inr; apply And.left; exact hqr
      . cases h1 with
        | inl hp => apply Or.inl; exact hp
        | inr hqr => apply Or.inr; apply And.right; exact hqr

    -- backward
    . intro h2
      cases h2 with
      | intro hpq hpr =>
        cases hpq with
        | inl hp => apply Or.inl; exact hp
        | inr hq => cases hpr with
          | inl hp => apply Or.inl; exact hp
          | inr hr => apply Or.inr; apply And.intro; exact hq; exact hr


theorem or_distributes_over_and_r (p q r : Prop) :
    (p ∧ q) ∨ r ↔ (p ∨ r) ∧ (q ∨ r) := by
    apply Iff.intro
    -- forward
    . intro h1
      apply And.intro
      . cases h1 with
        | inl hpq => apply Or.inl; apply And.left; exact hpq
        | inr hr => apply Or.inr; exact hr
      . cases h1 with
        | inl hpq => apply Or.inl; apply And.right; exact hpq
        | inr hr => apply Or.inr; exact hr

    -- backward
    . intro h2
      cases h2 with
      | intro hpr hqr =>
        cases hqr with
        | inr hr => apply Or.inr; exact hr
        | inl hq =>
          cases hpr with
          | inr hr => apply Or.inr; exact hr
          | inl hp => apply Or.inl; apply And.intro; exact hp; exact hq
