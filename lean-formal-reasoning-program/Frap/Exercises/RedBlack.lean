-- red-black trees exercises

import Frap.RedBlack

namespace Tree

/-
exercise (2-star)
Prove that `insert` preserves `BST.
You do not need induction.
You might need to use `unfold` to unfold the definition of a function.
-/
#check ins_BST
theorem insert_BST {α : Type u} (t : Tree α) k vk
    : BST t → BST (insert k vk t) := by
  intro hbst
  unfold insert
  have lemma {α : Type u} (t : Tree α) k vk : (ins k vk t).BST = (ins k vk t).make_black.BST := by
    rw [make_black]
    split
    . simp [*]
    . simp [ins]
      constructor
      . intro h
        simp [*] at h
        rcases h <;>
        constructor <;> assumption
      . intro h
        simp [*]
        rcases h <;>
        constructor <;> assumption
  rw [←lemma]
  apply ins_BST
  exact hbst

/-
exercise (2-star)
Verify the second and third equations for `insert`.
You may use unproven theorems in the imported file, though you are encouraged to do so.
You might need to prove a lemma.
-/

theorem lookup_insert_eq {α : Type u} (d : α) t k vk
    : BST t → lookup d k (insert k vk t) = vk := by
  intro h
  unfold insert
  have lemma {α : Type u} (d : α) (t : Tree α) k vk : lookup d k (ins k vk t) = lookup d k (ins k vk t).make_black := by
    rw [make_black]
    unfold lookup
    split <;> rfl
  rw [←lemma]
  apply lookup_ins_eq
  exact h

theorem lookup_insert_neq {α : Type u} (d : α) t k vk
    : BST t → k ≠ k' → lookup d k' (insert k vk t) = lookup d k' t := by
  intros hbst hneq
  unfold insert
  have lemma {α : Type u} (d : α) (t : Tree α) k vk k' : lookup d k' (ins k vk t) = lookup d k' (ins k vk t).make_black := by
    rw [make_black]
    unfold lookup
    split <;> rfl
  rw [←lemma]
  apply lookup_ins_neq
  . exact hbst
  . exact hneq

end Tree
