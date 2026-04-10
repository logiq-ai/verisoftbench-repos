-- linear logic exercises

import Frap.LinearLogic

open LinearTerm
open Permutation
open ValidLinearJudgment

theorem tensor_dist_plus_r' a b c : [] ⊩ (a ⊕ b) ⊗ c ≣ (a ⊗ c) ⊕ (b ⊗ c) := by
  apply vl_with_i
  . apply vl_lolli_i -- [] ++ [(a ⊕ b) ⊗ c] ⊩ a ⊗ c ⊕ b ⊗ c
    apply vl_exchange ([(a ⊕ b) ⊗ c] ++ [])
    . apply permutation_refl
    . apply vl_tensor_e
      . apply vl_hyp
      . apply vl_exchange ([a ⊕ b] ++ [c])
        . apply permutation_refl
        . apply vl_plus_e
          . apply vl_hyp
          . apply vl_exchange ([a] ++ [c])
            . apply perm_swap
            . apply vl_plus_il
              . apply vl_tensor_i
                . apply vl_hyp
                . apply vl_hyp
          . apply vl_exchange ([b] ++ [c])
            . apply perm_swap
            . apply vl_plus_ir
              apply vl_tensor_i
              . apply vl_hyp
              . apply vl_hyp

  . apply vl_lolli_i -- [] ++ [a ⊗ c ⊕ b ⊗ c] ⊩ (a ⊕ b) ⊗ c
    apply vl_exchange ([(a ⊗ c) ⊕ (b ⊗ c)] ++ [])
    . apply permutation_refl
    . apply vl_plus_e
      . apply vl_hyp
      . apply vl_exchange ([a ⊗ c] ++ [])
        . apply permutation_refl
        . apply vl_tensor_e
          . apply vl_hyp
          . apply vl_exchange ([a] ++ [c])
            . apply permutation_refl
            . apply vl_tensor_i
              . apply vl_plus_il
                apply vl_hyp
              . apply vl_hyp
      . apply vl_exchange ([b ⊗ c] ++ [])
        . apply permutation_refl
        . apply vl_tensor_e
          . apply vl_hyp
          . apply vl_exchange ([b] ++ [c])
            . apply permutation_refl
            . apply vl_tensor_i
              . apply vl_plus_ir
                apply vl_hyp
              . apply vl_hyp

theorem linear_curry' a b c : [(a ⊗ b) ⊸ c] ⊩ a ⊸ b ⊸ c := by
  apply vl_lolli_i
  apply vl_lolli_i
  apply vl_exchange ([a ⊗ b ⊸ c] ++ [a,b])
  . apply permutation_refl
  . apply vl_lolli_e (A:= a ⊗ b)
    . apply vl_hyp
    . apply vl_exchange ([a] ++ [b])
      . apply permutation_refl
      . apply vl_tensor_i
        . apply vl_hyp
        . apply vl_hyp

theorem unit_lolli_ident_l' a : [] ⊩ l_unit ⊸ a ≣ a := by
  apply vl_with_i
  . apply vl_lolli_i
    apply vl_exchange ([l_unit ⊸ a] ++ [])
    . apply permutation_refl
    . apply vl_lolli_e
      . apply vl_hyp
      . apply vl_unit_i
  . apply vl_lolli_i
    apply vl_lolli_i
    apply vl_exchange ([] ++ [l_unit] ++ [a])
    . apply perm_swap
    . apply vl_unit_e
      . apply vl_unit_e
        . apply vl_unit_i
        . apply vl_hyp
      . apply vl_hyp

/-
Prove that tensor, with, and plus are commutative.
-/

theorem tensor_comm a b : [] ⊩ a ⊗ b ≣ b ⊗ a := by
  have h a b : [] ⊩ a ⊗ b ⊸ b ⊗ a := by
    apply vl_lolli_i
    apply vl_exchange ([a ⊗ b] ++ [])
    . apply permutation_refl
    . apply vl_tensor_e
      . apply vl_hyp
      . apply vl_exchange ([b] ++ [a])
        . apply perm_swap
        . apply vl_tensor_i
          . apply vl_hyp
          . apply vl_hyp
  apply vl_with_i
  . apply h a b
  . apply h b a

theorem with_comm a b : [] ⊩ a & b ≣ b & a := by
  have h a b : [] ⊩ a & b ⊸ b & a := by
    apply vl_lolli_i
    apply vl_exchange ([a & b] ++ [])
    . apply permutation_refl
    . apply vl_with_i
      . apply vl_with_er
        . apply vl_hyp
      . apply vl_with_el
        . apply vl_hyp
  apply vl_with_i
  . apply h a b
  . apply h b a

theorem plus_comm a b : [] ⊩ a ⊕ b ≣ b ⊕ a := by
  have h a b : [] ⊩ a ⊕ b ⊸ b ⊕ a := by
    apply vl_lolli_i
    apply vl_exchange ([a ⊕ b] ++ [])
    . apply permutation_refl
    . apply vl_plus_e
      . apply vl_hyp
      . apply vl_plus_ir
        apply vl_hyp
      . apply vl_plus_il
        apply vl_hyp
  apply vl_with_i
  . apply h a b
  . apply h b a
