-- small-step operational semantics for Imp exercises

import Frap.SmallStepImp

namespace CImp
open Imp
open AStep
open BStep
open CStep
open Multi

/-
exercise (3-star)
-/

theorem par_body_n__Sn' n st
    : st x = n ∧ st y = 0
      → Multi CStep (par_loop, st) (par_loop, x !-> n + 1; st) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  apply multi_step
  . apply cs_par2; apply cs_while
  . apply multi_step
    . apply cs_par2; apply cs_ifStep
      apply bs_eq1; apply as_id
    . apply multi_step
      apply cs_par2; apply cs_ifStep
      apply bs_eq; apply multi_step
      . apply cs_par2; simp [*]; apply cs_ifTrue
      . apply multi_step
        . apply cs_par2; apply cs_seqStep; apply cs_asgnStep
          apply as_plus1; apply as_id
        . apply multi_step
          . apply cs_par2; apply cs_seqStep; apply cs_asgnStep -- perform x + 1
            apply as_plus
          . apply multi_step
            . apply cs_par2; apply cs_seqStep; simp[*] ; apply cs_asgn -- assign x = x + 1 will yield x = n + 1 due to x = n
            . apply multi_step
              . apply cs_par2; apply cs_seqFinish -- finish x = n + 1
              . unfold par_loop
                apply multi_refl -- done

/-
exercise (3-star)
-/

theorem par_body_n' n st
    : st x = 0 ∧ st y = 0
      → ∃ st', Multi CStep (par_loop, st) (par_loop, st')
          ∧ st' x = n ∧ st' y = 0 := by
  intro h
  obtain ⟨hx, hy⟩ := h
  induction n with
  | zero =>
      exists st
      apply And.intro
      . apply multi_refl
      . apply And.intro
        . apply hx
        . apply hy
  | succ n' hn' =>
      obtain ⟨st', ⟨h', ⟨hx', hy'⟩⟩⟩ := hn'
      constructor
      apply And.intro
      . apply multi_trans
        . apply h'
        . apply par_body_n__Sn
          . apply And.intro
            . exact hx'
            . exact hy'
      . apply And.intro
        . rfl
        . exact hy'
