import Mathlib.Data.Finmap
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Nodup

import SPLean.Common.Util
import SPLean.Theories.Lang


/- ========= Useful Lemmas about disjointness and state operations ========= -/

lemma disjoint_update_not_r (h1 h2 : state) (x : loc) (v: val) :
  Finmap.Disjoint h1 h2 →
  x ∉ h2 →
  Finmap.Disjoint (Finmap.insert x v h1) h2 :=
by
  srw Finmap.Disjoint => ??
  srw Finmap.Disjoint Finmap.mem_insert => ?
  sby scase

lemma in_read_union_l (h1 h2 : state) (x : loc) :
  x ∈ h1 → read_state x (h1 ∪ h2) = read_state x h1 :=
by
  move=> ?
  srw []read_state
  sby srw (Finmap.lookup_union_left)

lemma disjoint_insert_l (h1 h2 : state) (x : loc) (v : val) :
  Finmap.Disjoint h1 h2 →
  x ∈ h1 →
  Finmap.Disjoint (Finmap.insert x v h1) h2 :=
by
  srw Finmap.Disjoint => *
  srw Finmap.Disjoint Finmap.mem_insert => ?
  sby scase

lemma insert_disjoint_l (h1 h2 : state) (x : loc) (v : val) :
  h2.Disjoint (h1.insert x v) →
  x ∉ h2 ∧ h2.Disjoint h1 := by
  unfold Finmap.Disjoint=> hdis ⟨|⟩
  { sby unfold Not=> /hdis }
  sby move=> >

lemma remove_disjoint_union_l (h1 h2 : state) (x : loc) :
  x ∈ h1 → Finmap.Disjoint h1 h2 →
  Finmap.erase x (h1 ∪ h2) = Finmap.erase x h1 ∪ h2 :=
by
  srw Finmap.Disjoint => * ; apply Finmap.ext_lookup => y
  scase: [x = y]=> hEq
  { scase: [y ∈ Finmap.erase x h1]=> hErase
    { srw Finmap.lookup_union_right
      rw [Finmap.lookup_erase_ne]
      apply Finmap.lookup_union_right
      srw Finmap.mem_erase at hErase=>//
      srw Not at * => * //
      sby srw Not }
    srw Finmap.lookup_union_left
    sby sdo 2 rw [Finmap.lookup_erase_ne] }
  srw -hEq
  srw Finmap.lookup_union_right=>//
  srw Finmap.lookup_erase
  apply Eq.symm
  sby srw Finmap.lookup_eq_none

lemma remove_not_in_l (h1 h2 : state) (p : loc) :
  p ∉ h1 →
  (h1 ∪ h2).erase p = h1 ∪ h2.erase p := by
  move=> ?
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> ?
    srw Finmap.lookup_erase_ne=> //
    scase: [x ∈ h1]
    { move=> ? ; sby srw ?Finmap.lookup_union_right }
    move=> ? ; sby srw ?Finmap.lookup_union_left }
  move=> ->
  sby srw Finmap.lookup_union_right

lemma remove_not_in_r (h1 h2 : state) (p : loc) :
  p ∉ h2 →
  (h1 ∪ h2).erase p = h1.erase p ∪ h2 := by
  move=> ?
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> ?
    srw Finmap.lookup_erase_ne=> //
    scase: [x ∈ h1]
    { move=> ? ; sby srw ?Finmap.lookup_union_right }
    move=> ? ; sby srw ?Finmap.lookup_union_left }
  move=> ->
  sby srw Finmap.lookup_union_left_of_not_in

lemma disjoint_remove_l (h1 h2 : state) (x : loc) :
  Finmap.Disjoint h1 h2 →
  Finmap.Disjoint (Finmap.erase x h1) h2 :=
by
  srw Finmap.Disjoint=> ??
  sby srw Finmap.mem_erase

lemma erase_disjoint (h1 h2 : state) (p : loc) :
  h1.Disjoint h2 →
  (h1.erase p).Disjoint h2 := by
  sby unfold Finmap.Disjoint=> ?? > /Finmap.mem_erase

lemma disjoint_single (h : state) :
  p ∉ h →
  h.Disjoint (Finmap.singleton p v) := by
  move=> ?
  unfold Finmap.Disjoint=> > ?
  sby scase: [x = p]

lemma insert_union (h1 h2 : state) (p : loc) (v : val) :
  p ∉ h1 ∪ h2 →
  (h1 ∪ h2).insert p v = (h1.insert p v) ∪ h2 := by
  move=> ?
  apply Finmap.ext_lookup=> >
  scase: [x = p]=> ?
  { srw Finmap.lookup_insert_of_ne=> //
    scase: [x ∈ h1]=> ?
    { sby srw ?Finmap.lookup_union_right }
    sby srw ?Finmap.lookup_union_left }
  sby subst x

lemma insert_mem_keys (s : state) :
  p ∈ s →
  (s.insert p v).keys = s.keys := by
  move=> ?
  apply Finset.ext=> >
  sby srw ?Finmap.mem_keys

lemma non_mem_union (h1 h2 : state) :
  a ∉ h1 ∪ h2 ↔ a ∉ h1 ∧ a ∉ h2 := by sdone

lemma insert_delete_id (h : state) (p : loc) :
  p ∉ h →
  h = (h.insert p v).erase p := by
  move=> hin
  apply Finmap.ext_lookup=> >
  scase: [x = p]=> ?
  { sby srw Finmap.lookup_erase_ne }
  subst x
  move: hin=> /Finmap.lookup_eq_none ?
  sby srw Finmap.lookup_erase

lemma insert_same (h1 h2 : state) :
  p ∉ h1 → p ∉ h2 →
  (h1.insert p v).keys = (h2.insert p v').keys →
  h1.keys = h2.keys := by
  move=> ?? /Finset.ext_iff
  srw Finmap.mem_keys Finmap.mem_insert=> hin
  apply Finset.ext=> > ; srw ?Finmap.mem_keys
  scase: [a = p]=> ?
  { apply Iff.intro
    sdo 2 (sby move=> /(Or.intro_right (a = p)) /hin []) }
  sby subst a

lemma insert_same_eq (h1 h2 : state) :
  p ∉ h1 → p ∉ h2 →
  h1.insert p v = h2.insert p v →
  h1 = h2 := by
  move=> /Finmap.lookup_eq_none ? /Finmap.lookup_eq_none ? *
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> /Finmap.lookup_insert_of_ne hlook
    sby srw -(hlook _ v h1) -(hlook _ v h2) }
  sby move=> []

lemma union_same_keys (h₁ h₂ h₃ : state) :
  h₁.Disjoint h₃ → h₂.Disjoint h₃ →
  (h₁ ∪ h₃).keys = (h₂ ∪ h₃).keys →
  h₁.keys = h₂.keys := by
  unfold Finmap.Disjoint
  move=> ?? /Finset.ext_iff
  srw Finmap.mem_keys Finmap.mem_union=> hin
  apply Finset.ext=> > ; srw ?Finmap.mem_keys
  apply Iff.intro
  sdo 2 (sby move=> /[dup] ? /(Or.intro_left (a ∈ h₃)) /hin [])

lemma insert_eq_union_single (h : state) :
  p ∉ h →
  h.insert p v = h ∪ (Finmap.singleton p v) := by
  move=> ?
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> ?
    srw Finmap.lookup_insert_of_ne=> //
    sby srw Finmap.lookup_union_left_of_not_in }
  sby move=> []

lemma keys_eq_not_mem_r (h1 h2 : state) :
  h1.keys = h2.keys →
  p ∉ h2 →
  p ∉ h1 := by
  move=> /Finset.ext_iff
  sby srw Finmap.mem_keys

lemma keys_eq_not_mem_l (h1 h2 : state) :
  h1.keys = h2.keys →
  p ∉ h1 →
  p ∉ h2 := by
  move=> /Finset.ext_iff
  sby srw Finmap.mem_keys

lemma keys_eq_mem_r (h1 h2 : state) :
  h1.keys = h2.keys →
  p ∈ h2 →
  p ∈ h1 := by
  move=> /Finset.ext_iff
  sby srw Finmap.mem_keys

lemma state_eq_not_mem (p : loc) (h1 h2 : state) :
  h1 = h2 →
  p ∉ h1 →
  p ∉ h2 := by sdone

lemma erase_of_non_mem (h : state) :
  p ∉ h →
  h.erase p = h := by
  move=> /Finmap.lookup_eq_none ?
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> /Finmap.lookup_erase_ne Hlook
    srw Hlook }
  move=> []
  sby srw Finmap.lookup_erase

lemma insert_neq_of_non_mem (h : state) :
  x ∉ h →
  x ≠ p →
  x ∉ h.insert p v := by
  move=> * ; unfold Not
  sby move=> /Finmap.mem_insert

lemma reinsert_erase_union (h1 h2 h3 : state) :
  h3.lookup p = some v →
  p ∉ h2 →
  h3.erase p = h1 ∪ h2 →
  h3 = (h1.insert p v) ∪ h2 := by
  move=> ?? heq
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> /[dup] /Finmap.lookup_erase_ne hlook
    srw -hlook {hlook} heq
    scase: [x ∈ h1]
    { sby move=> * ; srw ?Finmap.lookup_union_right }
    move=> * ; sby srw ?Finmap.lookup_union_left }
  move=> []
  sby srw Finmap.lookup_union_left

lemma union_singleton_eq_erase (h h' : state) :
  h.Disjoint (Finmap.singleton p v) →
  h' = h ∪ Finmap.singleton p v →
  h = h'.erase p := by
  move=> hdisj []
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> ?
    srw Finmap.lookup_erase_ne=> //
    sby srw Finmap.lookup_union_left_of_not_in }
  move=> []
  srw Finmap.lookup_erase
  srw Finmap.lookup_eq_none
  sby move: hdisj ; unfold Finmap.Disjoint Not=> /[apply]

lemma union_singleton_eq_insert (h : state) :
  Finmap.singleton p v ∪ h = h.insert p v := by
  apply Finmap.ext_lookup=> >
  sby scase: [x = p]

lemma disjoint_keys (h₁ h₂ : state) :
  h₁.Disjoint h₂ →
  Disjoint h₁.keys h₂.keys := by
  unfold Finmap.Disjoint
  srw -Finmap.mem_keys Finset.disjoint_iff_ne
  move=> hFmap > /hFmap ? > hb
  sby srw Not

lemma non_mem_diff_helper1 (h₁ : state) (l : @AList loc fun _ ↦ val) :
  a ∉ l →
  p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) (Finmap.erase a h₁) l.entries →
  p ≠ a := by
  elim: l h₁=> //
  move=> > ? ih > /== ??
  srw Finmap.erase_erase
  srw List.kerase_of_not_mem_keys=> // ?
  sby apply ih

lemma non_mem_diff_helper2 (h₁ : state) (l : @AList loc fun _ ↦ val) :
  p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) (Finmap.erase a h₁) l.entries →
  p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) h₁ l.entries := by
  elim: l h₁=> //
  move=> > ? ih >
  srw AList.insert_entries List.foldl_cons=> /=
  srw List.kerase_of_not_mem_keys=> // ?
  apply ih
  sby srw Finmap.erase_erase

theorem mem_diff_r (h₁ h₂ : state) :
  p ∈ h₁ \ h₂ → p ∉ h₂ := by
  refine Finmap.induction_on h₂ ?
  move=> >
  unfold Finmap.instSDiff Finmap.sdiff Finmap.foldl=> /==
  elim: a
  { sdone }
  move=> > ih1 ih2
  srw AList.insert_entries List.foldl_cons=> /=
  srw List.kerase_of_not_mem_keys=> //== ? ⟨|⟩
  { sby apply non_mem_diff_helper1 }
  apply ih2
  sby apply non_mem_diff_helper2

lemma mem_erase_right (s : state) :
  p ∈ s.erase x → p ∈ s := by
  sby move=> /Finmap.mem_erase

lemma list_foldl_erase_mem (h₁ : state) (l : @AList loc fun _ ↦ val) :
  p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) h₁ l.entries → p ∈  h₁ := by
  elim: l h₁=> //
  move=> > ? ih /=
  srw List.kerase_of_not_mem_keys=> // > /ih
  sby srw Finmap.mem_erase

lemma mem_diff_helper (h₁ : state) (l : @AList loc fun _ ↦ val) :
  a ∉ l →
  (p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) h₁ l.entries → p ∈ h₁) →
  p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) (Finmap.erase a h₁) l.entries →
  p ∈ h₁ := by
  elim: l h₁=> >
  { sdone }
  move=> ? ih > /== ?
  srw List.kerase_of_not_mem_keys=> //
  srw Finmap.erase_erase=> ???
  apply (@mem_erase_right p a_1 h₁)
  sby apply ih=> // /list_foldl_erase_mem

theorem mem_diff_l (h₁ h₂ : state) :
  p ∈ h₁ \ h₂ → p ∈ h₁ := by
  refine Finmap.induction_on h₂ ? _
  move=> >
  unfold Finmap.instSDiff Finmap.sdiff Finmap.foldl=> /=
  elim: a=> > //
  move=> ? ih
  srw AList.insert_entries List.foldl_cons=> /=
  srw List.kerase_of_not_mem_keys=> //
  sby apply mem_diff_helper

lemma mem_diff_rev_helper (h₁ : state) (l : @AList loc fun _ ↦ val) :
  a ∉ l →
  (p ∈ h₁ ∧ p ∉ l.toFinmap → p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) h₁ l.entries) →
  p ∈ h₁ ∧ p ∉ (AList.insert a b l).toFinmap →
  p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) (Finmap.erase a h₁) l.entries := by
  elim: l h₁=> >
  { move=> ? /== _ ?
    unfold Not=> hsing ⟨| // ⟩
    move=> []
    apply hsing
    sby srw AList.mem_keys AList.keys_singleton }
  move=> ? ih > ? /=
  srw List.kerase_of_not_mem_keys=> // ?
  srw Finmap.erase_erase=> ?
  sby apply ih

theorem mem_diff_rev (h₁ h₂ : state) :
  p ∈ h₁ ∧ p ∉ h₂ → p ∈ h₁ \ h₂ := by
  refine Finmap.induction_on h₂ ? _
  move=> >
  unfold Finmap.instSDiff Finmap.sdiff Finmap.foldl=> /=
  elim: a=> > //
  move=> ? ih /=
  srw List.kerase_of_not_mem_keys=> // ?
  sby apply mem_diff_rev_helper

/- Main theorem about set difference for Finmaps -/
@[simp]
theorem mem_diff_iff (h₁ h₂ : state) :
  p ∈ h₁ \ h₂ ↔ p ∈ h₁ ∧ p ∉ h₂ := by
  apply Iff.intro
  { sby move=> /[dup] /mem_diff_l ? /mem_diff_r }
  apply mem_diff_rev

theorem diff_non_mem (h₁ h₂ : state) :
  p ∈ h₂ → p ∉ h₁ \ h₂ := by sdone

lemma union_difference_id (h₁ h₂ : state) :
  h₁.Disjoint h₂ →
  (h₁ ∪ h₂) \ h₂ = h₁ := by
  refine Finmap.induction_on h₂ ? _
  move=> >
  unfold Finmap.instSDiff Finmap.sdiff Finmap.foldl=> /=
  elim: a=> > //== ?
  srw List.kerase_of_not_mem_keys=> // ih
  srw -Finmap.insert_toFinmap=> /insert_disjoint_l ?
  srw remove_not_in_l=> //
  sby srw -insert_delete_id

lemma diff_disjoint (h₁ h₂ : state) :
  h₂.Disjoint (h₁ \ h₂) := by sdone

lemma disjoint_disjoint_diff (h₁ h₂ h₃ : state) :
  h₁.Disjoint h₂ →
  (h₁ \ h₃).Disjoint h₂ := by
  sby unfold Finmap.Disjoint

lemma lookup_diff (h₁ h₂ : state) :
  p ∉ h₂ →
  (h₁ \ h₂).lookup p = h₁.lookup p := by
  refine Finmap.induction_on h₂ ? _
  move=> >
  unfold Finmap.instSDiff Finmap.sdiff Finmap.foldl=> /==
  elim: a h₁=> > //
  move=> ? ih > /=
  sby srw List.kerase_of_not_mem_keys

lemma lookup_diff_none (h₁ h₂ : state) :
  p ∈ h₂ →
  (h₁ \ h₂).lookup p = none := by
  sby move=> /(diff_non_mem h₁) /Finmap.lookup_eq_none

lemma union_diff_disjoint_r (h₁ h₂ h₃ : state) :
  h₂.Disjoint h₃ →
  (h₁ ∪ h₂) \ h₃ = (h₁ \ h₃) ∪ h₂ := by
  unfold Finmap.Disjoint=> hdis
  apply Finmap.ext_lookup=> >
  scase: [x ∈ h₃]
  { move=> ?
    scase: [x ∈ h₁]
    { move=> ? ; sby srw lookup_diff }
    move=> ? ; srw Finmap.lookup_union_left=> //
    sby srw ?lookup_diff }
  move=> ?
  scase: [x ∈ h₂]
  { move=> ? ; srw Finmap.lookup_union_left_of_not_in=> //
    sby srw ?lookup_diff_none }
  sby move=> /hdis

  lemma diff_disjoint_eq (s₁ s₂ s₃ : state) :
  s₁.Disjoint s₂ →
  s₂.keys = s₃.keys →
  (s₁ ∪ s₂) \ s₃  = s₁ := by
  srw Finmap.Disjoint.symm_iff Finmap.Disjoint=> hdis
  srw Finset.ext_iff Finmap.mem_keys=> hsub
  apply Finmap.ext_lookup=> >
  scase: [x ∈ s₃]
  { move=> /[dup] ? /lookup_diff ->
    srw Finmap.lookup_union_left_of_not_in
    sby unfold Not=> /hsub }
  move=> /[dup] /hsub /hdis /Finmap.lookup_eq_none ->
  sby move=> /lookup_diff_none

  lemma intersect_comm (s2 d : state) (a₁ : loc) (b₁ : val) (a₂ : loc) (b₂ : val) :
  (fun s x _ ↦ if x ∈ s2 then s else Finmap.erase x s)
      ((fun s x _ ↦ if x ∈ s2 then s else Finmap.erase x s) d a₁ b₁) a₂ b₂ =
    (fun s x _ ↦ if x ∈ s2 then s else Finmap.erase x s)
      ((fun s x _ ↦ if x ∈ s2 then s else Finmap.erase x s) d a₂ b₂) a₁ b₁ := by
  dsimp
  scase: [a₁ ∈ s2]=> > /=
  scase: [a₂ ∈ s2]=> > /=
  apply Finmap.erase_erase

def intersect (s1 s2 : state) := s1 \ (s1 \ s2)

def st1 : state := (Finmap.singleton 0 1).insert 1 1
def st2 : state := ((Finmap.singleton 0 2).insert 2 2).insert 1 2
-- #reduce intersect st1 st2

lemma insert_eq_union_singleton (s : state) :
  p ∉ s →
  s.insert p v = Finmap.singleton p v ∪ s := by
  move=> ?
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> ?
    sby srw Finmap.lookup_insert_of_ne }
  move=> ->
  sby srw Finmap.lookup_insert Finmap.lookup_union_left_of_not_in

lemma AList_erase_entries (l : @AList loc (fun _ ↦ val)) :
  (l.erase p).entries = (l.entries).kerase p := by sdone

lemma Alist_insert_delete_id (l : @AList loc (fun _ ↦ val)) :
  p ∉ l →
  (l.insert p v).erase p = l := by
  move=> ?
  elim: l p v=> > /==
  { move=> >
    apply AList.ext=> /=
    sby srw AList_erase_entries }
  move=> ? ? > ??>
  apply AList.ext=> /==
  srw AList_erase_entries=> /==
  sby srw List.kerase_of_not_mem_keys

lemma intersect_foldl_mem (s₂ : state) (l₁ l₂ : @AList loc fun _ ↦ val):
  p ∈ List.foldl (fun d s ↦ if s.fst ∈ s₂ then d else Finmap.erase s.fst d)
    l₁.toFinmap l₂.entries →
  p ∈ l₁ := by
  elim: l₂ l₁=> > //
  move=> ? ih /==
  srw List.kerase_of_not_mem_keys=> // >
  sby scase_if=> // ? /ih

-- lemma intersect_mem_l (s₁ s₂ : state) :
--   p ∈ (intersect s₁ s₂) → p ∈ s₁ := by
--   refine Finmap.induction_on s₁ ? _
--   move=> >
--   unfold intersect Finmap.foldl=> /==
--   elim: a=> //=
--   move=> > ? ih
--   srw List.kerase_of_not_mem_keys=> //
--   scase_if=> ? /==
--   { sby move=> /intersect_foldl_mem }
--   sby srw Alist_insert_delete_id

-- lemma intersect_mem_r_helper (s₂ : state) (l : @AList loc fun _ ↦ val) :
--   (p ∈ List.foldl (fun d s ↦ if s.fst ∈ s₂ then d else Finmap.erase s.fst d)
--     l.toFinmap l.entries → p ∈ s₂) →
--   a ∈ s₂ →
--   p ∈ List.foldl (fun d s ↦ if s.fst ∈ s₂ then d else Finmap.erase s.fst d)
--     (AList.insert a b l).toFinmap l.entries →
--   p ∈ s₂ := by
--   elim: l=> > /==
--   { sby move=> _ ? /AList.mem_keys }
--   move=> ? ih1 >
--   srw List.kerase_of_not_mem_keys=> //
--   move=> ih2 ?
--   sorry

-- lemma intersect_foldl_mem_s2 (s₂ : state) (l₁ : @AList loc fun _ ↦ val) :
--   p ∈ List.foldl (fun d s ↦ if s.fst ∈ s₂ then d else Finmap.erase s.fst d)
--     l₁.toFinmap l₁.entries →
--   p ∈ s₂ := by
--   elim: l₁=> // >
--   move=> ? ih /==
--   srw Alist_insert_delete_id=> //
--   srw List.kerase_of_not_mem_keys=> //
--   scase_if=> ? //
--   sorry

-- lemma intersect_mem_r (s₁ s₂ : state) :
--   p ∈ (intersect s₁ s₂) → p ∈ s₂  := by
--   refine Finmap.induction_on s₁ ? _
--   move=> >
--   unfold intersect Finmap.foldl=> /=
--   elim: a=> > //=
--   move=> ? ih
--   srw List.kerase_of_not_mem_keys=> //==
--   srw Alist_insert_delete_id=> //
--   scase_if=> //
--   move: ih=> /== /intersect_mem_r_helper ih
--   specialize (ih a b)
--   sby move=> /ih

-- lemma mem_intersect :
--   p ∈ s₁ ∧ p ∈ s₂ → p ∈ (intersect s₁ s₂) := by
--   refine Finmap.induction_on s₁ ? _
--   move=> >
--   unfold intersect Finmap.foldl=> /==
--   elim: a=> > //? ih ? /==
--   move=> ?
--   srw Alist_insert_delete_id=> //
--   srw List.kerase_of_not_mem_keys=> //
--   sorry

@[simp]
lemma intersect_mem_iff (s₁ s₂ : state) :
  p ∈ (intersect s₁ s₂) ↔ p ∈ s₁ ∧ p ∈ s₂ := by srw intersect !mem_diff_iff //
  -- apply Iff.intro
  -- { sby move=> /[dup] /intersect_mem_l ? /intersect_mem_r }
  -- apply mem_intersect

lemma lookup_intersect (s₁ s₂ : state) :
  p ∈ s₁ ∧ p ∈ s₂ →
  (intersect s₁ s₂).lookup p = s₁.lookup p := by
  move=> []h1 h2
  srw intersect lookup_diff //
  -- refine Finmap.induction_on s₁ ? _
  -- move=> >
  -- unfold intersect Finmap.foldl=> /==
  -- elim: a=> > //
  -- move=> ? ih /==
  -- scase_if=> ? ; srw List.kerase_of_not_mem_keys=> //
  -- { sorry }
  -- srw Alist_insert_delete_id=> //
  -- sorry

lemma diff_insert_intersect_id (s₁ s₂ : state) :
  (s₁ \ s₂) ∪ (intersect s₁ s₂) = s₁ := by
  apply Finmap.ext_lookup=> >
  scase: [x ∈ s₁]
  { move=> /[dup] ? /Finmap.lookup_eq_none ->
    srw Finmap.lookup_union_right=> //
    have eqn:(x ∉ intersect s₁ s₂) := by sdone
    sby move: eqn=> /Finmap.lookup_eq_none }
  move=> ?
  scase: [x ∈ s₂]=> ?
  { srw Finmap.lookup_union_left=> //
    sby srw lookup_diff }
  srw Finmap.lookup_union_right=> //
  sby srw lookup_intersect

lemma union_monotone_r (s₃ s₁ s₂ : state) :
  s₁ = s₂ →
  s₁ ∪ s₃ = s₂ ∪ s₃ := by sdone

lemma non_mem_union' (s₁ s₂ : state) :
  x ∉ s₁ → x ∉ s₂ → x ∉ s₁ ∪ s₂ := by sdone

lemma union_same_eq_r (s₁ s₂ s₃ : state) :
  s₁.Disjoint s₃ →
  s₂.Disjoint s₃ →
  s₁ ∪ s₃ = s₂ ∪ s₃ →
  s₁ = s₂ := by
  move=> hdis₁ hdis₂ heq
  apply Finmap.ext_lookup=> >
  scase: [x ∈ s₁]
  { move=> /[dup] /Finmap.lookup_eq_none ->
    scase: [x ∈ s₃]
    { move=> h /non_mem_union'
      move: h=> /[swap] /[apply]
      sby srw heq=> /== /Finmap.lookup_eq_none }
    sby srw Finmap.Disjoint.symm_iff at hdis₂=> /hdis₂ /Finmap.lookup_eq_none }
  move=> /[dup] /hdis₁ ? /Finmap.lookup_union_left h
  specialize h s₃ ; sby srw -h heq Finmap.lookup_union_left_of_not_in

lemma disjoint_intersect_r (s₁ s₂ s₃ : state) :
  s₂.Disjoint s₃ →
  (intersect s₁ s₂).Disjoint s₃ := by
  sby unfold Finmap.Disjoint

lemma intersect_disjoint_cancel (s₁ s₂ s₃ : state) :
  s₁.Disjoint s₃ →
  (s₁ ∪ intersect s₂ s₃) \ s₃ = s₁ := by
  unfold Finmap.Disjoint=> hdis
  apply Finmap.ext_lookup=> >
  scase: [x ∈ s₁]
  { move=> /[dup] ? /Finmap.lookup_eq_none ->
    scase: [x ∈ s₃]
    { move=> ?
      srw lookup_diff=> //
      srw Finmap.lookup_union_right=> //
      sby srw Finmap.lookup_eq_none }
    sby move=> /lookup_diff_none }
  move=> /[dup] ? /hdis ?
  sby srw lookup_diff
