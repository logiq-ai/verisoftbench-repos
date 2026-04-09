-- Hoare logic exercises

import Frap.Hoare

namespace Imp
namespace Hoare
open AExp
open BExp
open Com
open CEval
attribute [local simp]
  aeval beval aequiv bequiv cequiv

/-
exercise (2-star)

The assignment rule looks backward to almost everyone the first time they see it.
If it still seems puzzling to you, it may help to think a little about alternative "forward" rules.
Here is a seemingly natural one:S
  `{ True } x := a { x = a }`

Give a counterexample showing that this rule is incorrect and use it to complete the proof below, showing that it is really a counterexample.
(Hint: The rule universally quantifies over the arithmetic expression `a`, and your counterexample needs to exhibit an `a` for which the rule doesn't work.)
-/

example : ∃ (a : AExp), ¬ (
    {* fun _ => True *}
      <{ x := <[a]> }>
    {* fun st => st x = aeval st a *}) := by
  let a := <{ x + 1 }>
  unfold valid_hoare_triple
  simp
  exists a
  simp
  -- intro h
  constructor
  . unfold x
    constructor
    . sorry
    . sorry
  . -- AExp is not a State ;∧;
    sorry
-- Ans : a = x + 1 is a counterexample showing that the rule is incorrect.

/-
Define `swap` program as follows.
-/

abbrev t := "t"
def swap_program : Com := <{
  t := x;
  x := y;
  y := t
}>

/-
exercise (2-star)
Prove that `swap` does what we expect.
-/

theorem swap_correct a₀ b₀ :
    {* fun st => st x = a₀ ∧ st y = b₀ *}
      swap_program
    {* fun st => st x = b₀ ∧ st y = a₀ *} := by
  unfold swap_program
  apply hoare_seq (fun st => st x = a₀ ∧ st y = b₀)
  apply hoare_asgn
  apply hoare_seq (fun st => st x = a₀ ∧ st y = b₀)
  apply hoare_asgn
  apply hoare_consequence_pre
  apply hoare_asgn
  intros st h
  simp [update]
  cases h; rename_i h₁ h₂
  constructor
  . apply h₂
  . apply h₁

/-
exercise (3-star)
Prove that `swap` satisfies the following specification.
-/

example :
    {* fun st => st x ≤ st y *}
      swap_program
    {* fun st => st y ≤ st x *} := by
  unfold swap_program
  apply hoare_seq (fun st => st x ≤ st y)
  apply hoare_asgn
  apply hoare_seq (fun st => st x ≤ st y)
  apply hoare_asgn
  apply hoare_consequence_pre
  apply hoare_asgn
  intros st h
  simp [update]
  apply h
