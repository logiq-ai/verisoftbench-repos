import Lean
import Mathlib.Data.Finmap

import SPLean.Common.Util

-- abbrev LabType := ℕ
local macro "LabType" : term => `(ℕ)

structure Labeled (α : Type*) where
  lab : LabType
  val : α

instance [Inhabited α] : Inhabited (Labeled α) := ⟨⟨0, default⟩⟩

def labSet (l : ℕ) (s : Set α) : Set (Labeled α) := { ⟨l, x⟩ | x ∈ s }

notation (priority := high) "⟪" l ", " s "⟫" => labSet l s

@[simp]
lemma labSet_diff (l : ℕ) (s s' : Set α) :
   ⟪l, s⟫ \ ⟪l, s'⟫ = ⟪l, s \ s'⟫ := by
  srw !labSet; apply Set.ext=>x; constructor=>//=
  -- { sby scase=>[w [H1 []]]Hn; exists w }
  -- sby scase=>w[H []]
  -- Who am I kidding? This how one should prove it:
  {aesop}
  aesop

@[simp]
lemma labSet_inter (l : ℕ) (s s' : Set α) :
  ⟪l, s⟫ ∩ ⟪l, s'⟫ = ⟪l, s ∩ s'⟫ := by
  srw !labSet; apply Set.ext=>x; constructor=>//==
  { aesop }
  aesop

@[simp]
lemma labSet_mem :
  x ∈ ⟪l, s⟫ ↔ x.lab = l ∧ x.val ∈ s := by
  simp [labSet]; constructor; aesop
  sby scase=><-?

@[disjE]
lemma disjoint_label_set :
  Disjoint ⟪l,s⟫ ⟪l',s'⟫ ↔ l ≠ l' ∨ Disjoint s s' := by
  simp [labSet]; constructor
  {
    move=>H; by_cases L: (l = l')=>//
    { subst l'; right=>w H1 H2
      let z := {x | ∃ y ∈ w, Labeled.mk l y = x}
      shave G: z ≤ ⊥
      { apply H; simp [z]
        {aesop}
        aesop }
      move: G; simp[z]
      srw Set.eq_empty_iff_forall_not_mem /== => H
      exact Set.subset_eq_empty H rfl }
  }
  scase=>H; srw Set.disjoint_iff_inter_eq_empty Set.eq_empty_iff_forall_not_mem=>x//==
  {aesop}
  move=>y1 H1 [y2] H2 Z; cases Z
  move: H
  sby srw Set.disjoint_iff_inter_eq_empty Set.eq_empty_iff_forall_not_mem
