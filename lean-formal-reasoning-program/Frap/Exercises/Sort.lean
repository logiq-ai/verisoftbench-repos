-- insertion sort exercises

import Frap.Sort

open Permutation
open Sorted

/-
exercise (2-star)
Prove the following fact by using only constructors in the `Permutation` relation.
-/
example : Permutation [1, 2, 3] [2, 3, 1] := by
  apply perm_trans
  . apply perm_swap  -- [1, 2, 3] ~ [2, 1, 3]
  . apply perm_skip  -- [1, 3] ~ [3, 1]
    apply perm_swap  -- [2, 1, 3] ~ [2, 3, 1]


/-
exercise (3-star)
Prove that insertion maintains sortedness.
-/

theorem insert_sorted' a l : Sorted l → Sorted (insert a l) := by
  intro S
  induction S with simp at *
  | sorted_nil => apply sorted_1
  | sorted_1 b =>
      split
      . constructor
        . assumption
        . apply sorted_1
      . constructor
        . omega
        . apply sorted_1
  | sorted_cons x y l' h₁ h₂ ih =>
    split
    . constructor
      . assumption
      . constructor
        . assumption
        . assumption
    . split
      . constructor
        . omega
        . constructor
          . omega
          . assumption
      . apply sorted_cons
        . omega
        . rename_i fls
          simp [*] at *
          apply ih

/-
exercise (2-star)
Using `insert_sorted`, prove the insertion sort makes a list sorted.
-/

theorem sort_sorted' l : Sorted (sort l) := by
  induction l with
  | nil => apply sorted_nil
  | cons n l ih =>
    apply insert_sorted'
    apply ih

/-
exercise (3-star)
Prove that `sort` is a permutation, using `insert_perm`.
-/

theorem sort_perm' l : Permutation l (sort l) := by
  induction l with simp [*] at *
  | nil => apply perm_nil
  | cons n al ih =>
    unfold sort
    split
    simp [*] at *
    . apply insert_perm
    . constructor
      . apply perm_skip
        . apply ih
      . constructor
        . apply insert_perm
        . simp
          apply permutation_refl


/-
exercise (1-star)
Finish the proof of correctness!
-/

theorem insertion_sort_correct' : is_a_sorting_algorithm sort := by
  unfold is_a_sorting_algorithm
  intro al
  apply And.intro
  . apply sort_perm
  . apply sort_sorted
