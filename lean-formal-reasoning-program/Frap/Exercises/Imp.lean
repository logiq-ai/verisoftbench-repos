-- imperative language exercises

import Frap.Imp

/-
Here, we will work with the original version of arithmetic and boolean expressions (before adding identifiers).
-/

namespace Hidden.AExp

open AExp
open BExp

/-
exercise (1-star)
Prove that the combination of the two optimizations involving zero still preserves the meaning of arithmetic expressions.
You may use results from the lecture without proofs.
-/

def optimize_plus_with_0 (a : AExp) : AExp :=
  optimize_plus0 (optimize_0plus a)

#check optimize_0plus
#check optimize_0plus_sound

theorem optimize_plus_with_0_sound (a : AExp)
    : aeval (optimize_plus_with_0 a) = aeval a := by
  simp [optimize_plus_with_0]
  simp [optimize_plus0_sound]
  apply optimize_0plus_sound

/-
exercise (3-star)
Since the `optimize_0plus` transformation doesn't change the value of `AExp`s, we should be able to apply it to all the `AExp`s that appear in a `BExp` without changing the `BExp`'s value.
Write a function that performs this transformation on `BExp`s and prove it is sound.
Use tactic combinators to make the proof as short and elegant as possible.
-/

def optimize_0plus_b (b : BExp) : BExp :=
  match b with
  | b_true => b
  | b_false => b
  | b_eq a₁ a₂ => b_eq (optimize_0plus a₁) (optimize_0plus a₂)
  | b_neq a₁ a₂ => b_neq (optimize_0plus a₁) (optimize_0plus a₂)
  | b_le a₁ a₂ => b_le (optimize_0plus a₁) (optimize_0plus a₂)
  | b_not b₁ => b_not (optimize_0plus_b b₁)
  | b_and b₁ b₂ => b_and (optimize_0plus_b b₁) (optimize_0plus_b b₂)
  | b_or b₁ b₂ => b_or (optimize_0plus_b b₁) (optimize_0plus_b b₂)

theorem optimize_0plus_b_sound (b : BExp)
    : beval (optimize_0plus_b b) = beval b := by
  induction b with
  | b_true => rfl
  | b_false => rfl
  | b_eq a₁ a₂ =>
      simp [optimize_0plus_b, beval]
      rw [optimize_0plus_sound a₁]
      rw [optimize_0plus_sound a₂]
  | b_neq a₁ a₂ =>
      simp [optimize_0plus_b, beval]
      rw [optimize_0plus_sound a₁]
      rw [optimize_0plus_sound a₂]
  | b_le a₁ a₂ =>
      simp [optimize_0plus_b, beval]
      rw [optimize_0plus_sound a₁]
      rw [optimize_0plus_sound a₂]
  | b_not b₁ ih =>
      simp [optimize_0plus_b, beval]
      rw [ih]
  | b_and b₁ b₂ ih₁ ih₂ =>
      simp [optimize_0plus_b, beval]
      rw [ih₁, ih₂]
  | b_or b₁ b₂ ih₁ ih₂ =>
      simp [optimize_0plus_b, beval]
      rw [ih₁, ih₂]

/-
exercise (3-star)
Write a relation `BEvalR` in the same style as `AEvalR`, and prove that it is equivalent to `beval`.
-/

-- def beval (b : BExp) : Bool :=
--   match b with
--   | b_true => true -- itself
--   | b_false => false -- itself
--   | b_eq a₁ a₂ => (aeval a₁) == (aeval a₂) -- Nat
--   | b_neq a₁ a₂ => (aeval a₁) != (aeval a₂) -- Nat
--   | b_le a₁ a₂ => (aeval a₁) <= (aeval a₂) -- Nat
--   | b_not b₁ => not (beval b₁) -- Bool
--   | b_and b₁ b₂ => and (beval b₁) (beval b₂) -- Bool
--   | b_or b₁ b₂ => or (beval b₁) (beval b₂) -- Bool

inductive BEvalR : BExp → Bool → Prop :=
  /- **fill in here** -/
  | e_b_true : BEvalR b_true true
  | e_b_false : BEvalR b_false false
  | e_b_eq (a₁ a₂ : AExp) (v₁ v₂ : Nat) : AEvalR a₁ v₁ → AEvalR a₂ v₂ → BEvalR (b_eq a₁ a₂) (v₁ == v₂)
  | e_b_neq (a₁ a₂ : AExp) (v₁ v₂ : Nat) : AEvalR a₁ v₁ → AEvalR a₂ v₂ → BEvalR (b_neq a₁ a₂) (v₁ != v₂)
  | e_b_le (a₁ a₂ : AExp) (v₁ v₂ : Nat) : AEvalR a₁ v₁ → AEvalR a₂ v₂ → BEvalR (b_le a₁ a₂) (v₁ <= v₂)
  | e_b_not (b : BExp) (v : Bool) : BEvalR b v → BEvalR (b_not b) (not v)
  | e_b_and (b₁ b₂ : BExp) (v₁ v₂ : Bool) : BEvalR b₁ v₁ → BEvalR b₂ v₂ → BEvalR (b_and b₁ b₂) (and v₁ v₂)
  | e_b_or (b₁ b₂ : BExp) (v₁ v₂ : Bool) : BEvalR b₁ v₁ → BEvalR b₂ v₂ → BEvalR (b_or b₁ b₂) (or v₁ v₂)

infix:90 " ==>b " => BEvalR

open BEvalR

theorem beval_iff_BEvalR b v
    : b ==>b v ↔ beval b = v := by
  constructor
  . intro h
    induction h <;> repeat simp [beval, *, aeval_iff_AEvalR] at *
  . intro h
    induction b generalizing v <;> simp [beval] at *
    . rw [h]; simp [e_b_true]
    . rw [h]; simp [e_b_false]
    . rw [←h]; simp [e_b_eq, aeval_iff_AEvalR]
    . rw [←h]; simp [e_b_neq, aeval_iff_AEvalR]
    . rw [←h]; simp [e_b_le, aeval_iff_AEvalR]
    . rw [←h]; constructor; assumption
    . rw [←h]; constructor <;> assumption
    . rw [←h]; constructor <;> assumption

end Hidden.AExp
