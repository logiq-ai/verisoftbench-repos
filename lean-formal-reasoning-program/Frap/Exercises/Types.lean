-- type systems exercises

import Frap.Types

namespace TM
open Tm
open BValue
open NValue
open Step
open Ty
open HasType

/-
exercise (3-star)
Complete the formal proof of the `progress` property.
-/
theorem progress'' t T
    : HasType t T → value t ∨ ∃ t', Step t t' := by
  intro ht
  induction ht with
  | t_if t₁ t₂ t₃ T =>
    rename_i ih₁ ih₂ ih₃
    right; cases ih₁
    . -- t₁ is a value
      have h : BValue t₁ := by
        apply bool_canonical <;> assumption
      cases h
      . exists t₂; apply st_ifTrue
      . exists t₃; apply st_ifFalse
    . -- t₁ can take a step
      rename_i h
      obtain ⟨t₁', h₁⟩ := h
      exists (ite t₁' t₂ t₃)
      apply st_if; exact h₁
  | t_true => left;unfold value; left; apply bv_true
  | t_false => left; unfold value; left; apply bv_false
  | t_0 => left; unfold value; right; apply nv_0
  | t_succ t =>
    rename_i ih
    cases ih
    . -- t is a value
      left
      have h : NValue t := by
        apply nat_canonical <;> assumption
      cases h
      . unfold value; right; apply nv_succ; apply nv_0
      . unfold value; right; apply nv_succ; apply nv_succ; assumption
    . -- t can take a step
      right
      rename_i ih
      obtain ⟨t', h⟩ := ih
      exists (scc t')
      apply st_succ; exact h
  | t_pred t =>
    rename_i ih
    right; cases ih
    . -- t is a value
      have h : NValue t := by
        apply nat_canonical <;> assumption
      cases h
      . exists zro; apply st_pred0
      . constructor; apply st_predSucc; assumption
    . -- t can take a step
      rename_i h
      obtain ⟨t', h⟩ := h
      exists (prd t')
      apply st_pred; exact h
  | t_iszero t =>
    rename_i ih
    right; cases ih
    . -- t is a value
      have h : NValue t := by
        apply nat_canonical <;> assumption
      cases h
      . exists tru; apply st_iszero0
      . exists fls; apply st_iszeroSucc; assumption
    . -- t can take a step
      rename_i h
      obtain ⟨t', h⟩ := h
      exists (iszero t')
      apply st_iszero; exact h

/-
exercise (2-star)
Complete the formal proof of the `preservation` property.
-/
theorem preservation'' t t' T
    : HasType t T → Step t t' → HasType t' T := by
  intro hT hE
  induction hT generalizing t' with
  | t_if =>
    rename_i ih₁ _ _
    cases hE
    . -- st_ifTrue
      assumption
    . -- st_ifFalse
      assumption
    . -- st_if
      apply t_if <;> try assumption
      apply ih₁; assumption
  | t_true => cases hE
  | t_false => cases hE
  | t_0 => cases hE
  | t_succ t =>
    rename_i ih
    cases hE
    apply t_succ
    apply ih
    assumption
  | t_pred t =>
    rename_i ih
    cases hE
    . apply t_0
    . rename_i hT
      cases hT
      assumption
    . apply t_pred
      apply ih
      assumption
  | t_iszero t =>
    rename_i ih
    cases hE
    . apply t_true
    . apply t_false
    . apply t_iszero
      apply ih
      assumption

/-
exercise (3-star)
Having seen the subject reduction property, one might wonder whether the opposite property—subject _expansion_—also holds.
That is, is it always the case that, if `t ~~> t'` and `⊢ t' ∈ T`, then `⊢ t ∈ T`?
If so, prove it.
If not, give a counterexample.
-/
theorem subject_expansion
    : (∀ t t' T, Step t t' ∧ HasType t' T → HasType t T)
      ∨ ¬ (∀ t t' T, Step t t' ∧ HasType t' T → HasType t T) := by
  right
  intros h
  have hT : ¬ HasType (ite fls zro tru) bool := by -- counterexample
    intro contra
    cases contra
    rename_i contra _
    cases contra
  apply hT
  apply h
  apply And.intro
  . apply st_ifFalse
  . apply t_true
