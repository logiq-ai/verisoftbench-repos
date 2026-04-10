-- trie exercises

import Frap.Trie

open Trie

/-
exercise (1-star)
-/
theorem look_leaf' α (d : α) j : look d j leaf = d := by
  unfold look
  rfl

/-
exercise (2-star)
This is a rather simple induction.
-/
local macro "simp'" : tactic =>
  `(tactic| (unfold ins look; simp [*] at *))

theorem look_ins_same' {α} d k (v : α) : ∀ t, look d k (ins d k v t) = v := by
  intro t
  induction k generalizing t with
  | xI k ih =>
    cases t <;> simp'
  | xO k ih =>
    cases t <;> simp'
  | xH =>
    cases t <;> simp'

/-
exercise (2-star)
Use `pos2nat2pos` and `nat2pos2nat` lemmas to prove the following injection properties.
-/

theorem pos2nat_injective' p q : pos2nat p = pos2nat q → p = q := by
  intro h
  rw [←pos2nat2pos p, ←pos2nat2pos q]
  rw [←h]

theorem nat2pos_injective' i j : nat2pos i = nat2pos j → i = j := by
  intro h
  rw [←nat2pos2nat i, ←nat2pos2nat j]
  rw [←h]
