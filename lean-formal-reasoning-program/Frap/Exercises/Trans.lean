-- program transformations exercises

import Frap.Trans

namespace Hidden.AExp
open AExp

/-
Recall the definition of `optimize_0plus` from the `Imp` lecture.
Note that this function is defined over the old version of `AExp`s, without states.
-/

-- def optimize_0plus (a : AExp) : AExp :=
--   match a with
--   | a_num _ => a
--   | a_plus (a_num 0) a₂ => optimize_0plus a₂
--   | a_plus a₁ a₂ => a_plus (optimize_0plus a₁) (optimize_0plus a₂)
--   | a_minus a₁ a₂ => a_minus (optimize_0plus a₁) (optimize_0plus a₂)
--   | a_mult a₁ a₂ => a_mult (optimize_0plus a₁) (optimize_0plus a₂)

-- def beval (st : State) (b : BExp) : Bool :=
--   match b with
--   | b_true => true
--   | b_false => false
--   | b_eq a₁ a₂ => (aeval st a₁) == (aeval st a₂)
--   | b_neq a₁ a₂ => (aeval st a₁) != (aeval st a₂)
--   | b_le a₁ a₂ => (aeval st a₁) <= (aeval st a₂)
--   | b_not b₁ => not (beval st b₁)
--   | b_and b₁ b₂ => and (beval st b₁) (beval st b₂)
--   | b_or b₁ b₂ => or (beval st b₁) (beval st b₂)

end Hidden.AExp

namespace Imp
open AExp
open BExp
open Com
open CEval
attribute [local simp]
  aeval beval aequiv bequiv cequiv

local macro "split'" : tactic =>
  `(tactic| split <;> (try rename_i heq; simp at heq; obtain ⟨⟩ := heq))

/-
Write a new version of this function that deals with variables (by leaving them along), plus analogous ones for `BExp`s and commands.
-/

def optimize_0plus_aexp (a : AExp) : AExp :=
  match a with
  | a_num _ => a
  | a_id _ => a
  | a_plus (a_num 0) a₂ => optimize_0plus_aexp a₂
  | a_plus a₁ a₂ => a_plus (optimize_0plus_aexp a₁) (optimize_0plus_aexp a₂)
  | a_minus a₁ a₂ => a_minus (optimize_0plus_aexp a₁) (optimize_0plus_aexp a₂)
  | a_mult a₁ a₂ => a_mult (optimize_0plus_aexp a₁) (optimize_0plus_aexp a₂)


def optimize_0plus_bexp (b : BExp) : BExp :=
  match b with
  | b_true => b_true
  | b_false => b_false
  | b_eq a₁ a₂ => b_eq (optimize_0plus_aexp a₁) (optimize_0plus_aexp a₂)
  | b_neq a₁ a₂ => b_neq (optimize_0plus_aexp a₁) (optimize_0plus_aexp a₂)
  | b_le a₁ a₂ => b_le (optimize_0plus_aexp a₁) (optimize_0plus_aexp a₂)
  | b_not b₁ => b_not (optimize_0plus_bexp b₁)
  | b_and b₁ b₂ => b_and (optimize_0plus_bexp b₁) (optimize_0plus_bexp b₂)
  | b_or b₁ b₂ => b_or (optimize_0plus_bexp b₁) (optimize_0plus_bexp b₂)

def optimize_0plus_com (c : Com) : Com :=
  match c with
  | c_skip => c_skip
  | c_asgn x a => c_asgn x (optimize_0plus_aexp a)
  | c_seq c₁ c₂ => c_seq (optimize_0plus_com c₁) (optimize_0plus_com c₂)
  | c_if b c₁ c₂ => c_if (optimize_0plus_bexp b) (optimize_0plus_com c₁) (optimize_0plus_com c₂)
  | c_while b c => c_while (optimize_0plus_bexp b) (optimize_0plus_com c)

/-
First, make sure that your optimization works with this example.
-/

example :
    optimize_0plus_com <{ while x != 0 do x := 0 + x - 1 end }>
    = <{ while x != 0 do x := x - 1 end }> := by
  simp [optimize_0plus_com, optimize_0plus_bexp, optimize_0plus_aexp]

/-
Prove that these three functions are sound, as we did or `fold_constants_×`.
Make sure you use the congruence lemmas in the proof of `optimize_0plus_com`; otherwise, it will be _long_!
-/

theorem optimize_0plus_aexp_sound : atrans_sound optimize_0plus_aexp := by
  intros a st
  induction a <;> simp [*, optimize_0plus_aexp] at *
  rename_i a₁ _ ih₁ ih₂
  induction a₁ <;> simp [*, optimize_0plus_aexp] at *
  rename_i Nat
  induction Nat <;> simp [*, optimize_0plus_aexp] at *


theorem optimize_0plus_bexp_sound : btrans_sound optimize_0plus_bexp := by
  intros b st
  induction b; rfl
  case b_false => rw [optimize_0plus_bexp]
  case b_eq a₁ a₂ => simp [*]; rw [optimize_0plus_aexp_sound a₁, optimize_0plus_aexp_sound a₂]
  case b_neq a₁ a₂ => simp [*]; rw [optimize_0plus_aexp_sound a₁, optimize_0plus_aexp_sound a₂]
  case b_le a₁ a₂ => simp [*]; rw [optimize_0plus_aexp_sound a₁, optimize_0plus_aexp_sound a₂]
  case b_not b' ih => simp [optimize_0plus_bexp]; rw [ih]
  case b_and b₁ b₂ ih₁ ih₂ => simp [optimize_0plus_bexp]; rw [ih₁, ih₂]
  case b_or b₁ b₂ ih₁ ih₂ => simp [optimize_0plus_bexp]; rw [ih₁, ih₂]


theorem optimize_0plus_com_sound : ctrans_sound optimize_0plus_com := by
  intros c
  induction c with simp [*] at *
  | c_skip => apply refl_cequiv
  | c_asgn => apply c_asgn_congruence; apply optimize_0plus_aexp_sound
  | c_seq =>
    apply c_seq_congruence
    . assumption
    . assumption
  | c_if =>
    apply c_if_congruence
    . apply optimize_0plus_bexp_sound
    . assumption
    . assumption
  | c_while =>
    apply c_while_congruence
    . apply optimize_0plus_bexp_sound
    . assumption

/-
Finally, let's define a compound optimizer on commands that first folds constatns (using `fold_constants_com`) and then eliminates `0 + n` terms (using `optimize_0plus_com`).
-/

def optimizer (c : Com) := optimize_0plus_com (fold_constants_com c)

/-
Prove that this optimizer is sound.
Hint: Use `trans_cequiv`.
-/

theorem optimizer_sound: ctrans_sound optimizer := by
  unfold ctrans_sound
  intros c st st'
  unfold optimizer
  apply trans_cequiv
  apply fold_constants_com_sound
  apply optimize_0plus_com_sound
