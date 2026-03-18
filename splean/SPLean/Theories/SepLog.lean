-- import Ssreflect.Lang
import Mathlib.Data.Finmap
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Nodup

import SPLean.Common.State

import SPLean.Common.Util
import SPLean.Theories.HProp
import SPLean.Theories.XSimp

open trm val prim

local instance : Coe val trm where
  coe v := trm.trm_val v

/- ================= Separation Logic Reasoning Rules ================= -/

/- -------------- Definition of Separation Logic Triples -------------- -/

abbrev triple (t : trm) (H : hProp) (Q : val → hProp) : Prop :=
  forall s, H s → eval s t Q

notation "funloc" p "↦" H =>
  fun (r : val) ↦ hexists (fun p ↦ ⌜r = val_loc p⌝ ∗ H)


/- ---------------- Structural Properties of [eval] ---------------- -/

section evalProp

set_option maxHeartbeats 2500000
/- Is there a good way to automate this? The current problem is that
   [constructor] does not always infer the correct evaluation rule to use.
   Since many of the rules involve a function application, using [constructor]
   often incorrectly applys eval_app_arg1, so we must instead manually apply
   the correct rule -/
lemma eval_conseq s t Q1 Q2 :
  eval s t Q1 →
  Q1 ===> Q2 →
  eval s t Q2 :=
by
  move=> heval
  srw (qimpl) (himpl)=> Imp
  elim: heval Q2
  { move=> * ; sby constructor }
  { move=> * ; sby constructor }
  { move=> * ; sby constructor }
  { move=> * ; sby constructor }
  { move=> * ; sby apply eval.eval_app_arg2 }
  { move=> * ; sby apply eval.eval_app_fun }
  { move=> * ; sby apply eval.eval_app_fix }
  { move=> * ; apply eval.eval_seq =>//
    move=> * ; aesop }
  { move=> * ; sby constructor }
  { move=> * ; sby constructor }
  { move=> * ; apply eval.eval_unop=>//
    sby srw (purepostin) at * }
  { move=> * ; apply eval.eval_binop=>//
    sby srw (purepostin) at * }
  { move=> * ; sby apply eval.eval_ref }
  { move=> * ; sby apply eval.eval_get }
  { move=> * ; sby apply eval.eval_set }
  { move=> * ; sby constructor }
  { move=> * ; sby apply eval.eval_alloc }
  { move=> * ; sby constructor }
  move=> * ; sby constructor


/- ============== Necessary Lemmas about [eval] and [evalExact] ============== -/

lemma finite_state (s : state) :
  ∃ p, p ∉ s := by
  scase: [s.keys.Nonempty]
  { srw Finset.nonempty_iff_ne_empty=> /== ?
    exists 0 ; unfold Not
    sby srw -Finmap.mem_keys }
  move=> /Finset.max_of_nonempty [>]
  have eqn:(w < w + 1) := by sdone
  move: eqn=> /Finset.not_mem_of_max_lt /[apply] ?
  exists (w + 1)

lemma conseq_ind (n : ℕ) (v : val) (p : loc) :
  x ∈ conseq (make_list n v) p → x ≥ p := by
  elim: n p=> > //
  move=> ih >
  unfold conseq make_list=> /== [] //
  move=> /ih ; omega

lemma finite_state' n (s : state) :
  ∃ p, p ≠ null ∧
    Finmap.Disjoint s (conseq (make_list n val_uninit) p) := by
  scase: [s.keys.Nonempty]
  { srw Finset.nonempty_iff_ne_empty=> /== ?
    exists 1 ; unfold null Finmap.Disjoint=> /== >
    sby srw -Finmap.mem_keys }
  move=> /Finset.max_of_nonempty [>] hmax
  exists (w + 1)=> ⟨|⟩
  { sby unfold null }
  unfold Finmap.Disjoint=> >
  move: hmax=> /[swap]
  srw -Finmap.mem_keys=> /Finset.le_max_of_eq /[apply] ?
  unfold Not=> /conseq_ind /==
  sby srw Nat.lt_succ_iff

lemma eval_sat :
  eval h t Q -> ∃ h v, Q h v := by
  elim=> // >
  { move=> ??? ![>?]; sapply=> // }
  { move=> ??? ![>?]; sapply=> // }
  { move=> ?? ![>?]; sapply=> // }
  { move=> ?? ![>?]; sapply=> // }
  { scase=> >
    any_goals move=> pp; (sdo 2 econstructor); apply pp=> // }
    -- move=> ? pp; sdo 2 econstructor; apply pp=> //}
  { scase=> >
    any_goals move=> pp; (sdo 2 econstructor); apply pp=> //
    any_goals move=> ? pp; (sdo 2 econstructor); apply pp=> // }
  { move=> ?? ![>] /[swap] /[apply]
    scase: (finite_state w_1)=> p hp
    sby move: hp=> /[swap] /[apply] ![>] }
  { sby move=> ??? ![>] /[swap] /[apply] }
  { move=> ?? /== ih
    scase: (finite_state' n.natAbs sa)
    sby move=> p [] /ih /[apply] ![>] }
  move=> ? /[swap]![>] /[swap] _ /[swap]/[apply]//

lemma evalExact_sat :
  evalExact s t Q → ∃ v s, Q v s := by
  elim=> > //
  { move=> _ _ _ ![] > /[swap] ; sapply }
  { move=> _ _ _ ![] > /[swap] ; sapply }
  { move=> _ _ ![] > /[swap] ; sapply }
  { move=> _ _ ![] > /[swap] ; sapply }
  { sby move=> [] }
  { sby move=> [] }
  { move=> ?? ![>] /[swap] /[apply]
    scase: (finite_state w_1)=> p hp
    sby move: hp=> /[swap] /[apply] ![>] }
  { sby move=> _ _ _ ![>] /[swap] /[apply] }
  { move=> ? _ /== ih
    scase: (finite_state' n.natAbs sa)
    sby move=> p [] /ih /[apply] ![>] }
  move=> ? /[swap]![>] /[swap] _ /[swap]/[apply]//

lemma evalExact_post :
  eval s t Q → evalExact s t Q' → Q' ===> Q:= by
  move=> H
  elim: H Q'=> >
  -- elim=> >
  { sby move=> ? > [] v h /== }
  { sby move=> ? > [] v h /== }
  { sby move=> ? > [] v h /== }
  { move=> ??? ih1 ih2 > [] // >
    { move=> > _ /[dup] h h'
      apply evalExact_sat in h=> ![] v s' /[dup] hQ1_1 hQ1_1'
      apply ih1 in h'=> himp hev
      apply himp in hQ1_1
      sby apply hev in hQ1_1'=> ? /ih2 }
    { move=> ?
      scase: op=> > ? //
      scase: a=> > ? // [] // }
    move=> ? [] // }
  { move=> ? _ _ ih1 ih2 > [] // > _ /[dup] h h'
    apply evalExact_sat in h=> ![] v s' /[dup] hQ1_1 hQ1_1'
    apply ih1 in h'=> himp hev
    apply himp in hQ1_1
    sby apply hev in hQ1_1'=> ? /ih2 }
  { sby move=> [] ?? > [] }
  { sby move=> [] ?? > [] }
  { move=> _ _ ih1 ih2 > [] > /[dup] h h'
    apply evalExact_sat in h=> ![] v s' > /[dup] hQ1_1 hQ1_1' hev
    apply ih1 in h'=> himp
    apply himp in hQ1_1
    sby apply hev in hQ1_1'=> ? /ih2 }
  { move=> _ _ ih1 ih2 > [] > /[dup] h /evalExact_sat ![] v s'
    move=> /[dup] hQ1_1 hQ1_1' hev
    apply ih1 in h=> himp
    apply himp in hQ1_1
    sby apply hev in hQ1_1'=> ? /ih2 }
  { sby move=> _ ih > [] }
  { unfold purepostin=> hOP ? > [] //
    apply evalunop_unique in hOP=> hP
    move=> > /hP []
    sby unfold purepost=> ?? }
  { unfold purepostin=> hOP ? > [] //
    { scase: op=> > //
      scase: a=> > // ? > ? [] // }
    apply evalbinop_unique in hOP=> hP
    move=> > /hP []
    sby unfold purepost=> ?? }
  { move=> ?? ih1 ih2 > [Q₁'] hevEx hev
    move=> > h
    move: hevEx hev
    move=> /[dup] /ih1 {} ih1 /evalExact_sat ![>] /[dup] /ih1 {}ih1
    move=> /[swap] /[apply]
    scase: (finite_state (h ∪ w_1))=> p /non_mem_union [] ? hp
    move: hp=> /[dup] hp /[swap] /[apply]
    move: ih1 hp=> /ih2 /[apply] {}ih2
    specialize (@ih2 fun v (s : state) ↦ Q' v (s.erase p))
    move: ih2=> /[apply]
    unfold qimpl himpl=> /== ?
    sby srw (insert_delete_id h p) }
  { sby move=> ?? > [] // _ ?? }
  { move=> [] ?? > [] //
    { move=> > ? [] // }
    sby move=> > _ [] ?? }
  { move=> ? _ _ ih1 ih2 > [] //
    move=> Q₁' ? /[dup] /ih1 {}ih1 /evalExact_sat ![>] /[dup] /ih1 {} ih1
    move=> /[swap] /[apply]
    sby move: ih1=> /ih2 }
  { move=> ? _ /== ih > hev
    move=> > h
    move: hev=> [] // _ /== hev
    scase: (finite_state' n.natAbs (sa ∪ h))
    move=> p [] /[dup] /ih {}ih /hev {}hev /Finmap.disjoint_union_left []
    move=> /[dup] /hev /[swap] /ih {}ih {hev} /ih {}ih /union_difference_id <-
    sby move=> /ih }
  { sby move=> ?? > [] }
  { move=> ?? ih1 ih2 > [] Q₁'
    move=> /[dup] /ih1 {}ih1 /evalExact_sat ![>] /[dup] /ih1 {}ih1
    move=> /[swap] /[apply]
    sby move: ih1=> /ih2 }

lemma evalExact_WellAlloc :
  evalExact s t Q →
  Q v s' →
  s'.keys = s.keys := by
  move=> hev
  elim: hev s' v
  { sby move=> > [] }
  { sby move=> > [] }
  { sby move=> > [] }
  { move=> > _ /evalExact_sat ![>] /[dup] hQ1 /[swap] _ /[swap] /[apply] heq
    move: hQ1=> /[swap] /[apply] /[apply]
    sby srw heq=> {}heq > /heq }
  { move=> > _ /evalExact_sat ![>] /[dup] hQ1 /[swap] _ /[swap] /[apply] heq
    move: hQ1=> /[swap] /[apply] /[apply]
    sby srw heq=> {}heq > /heq }
  { sby move=> > _ _ ih > /ih }
  { sby move=> > _ _ ih > /ih }
  { move=> > /evalExact_sat ![>] /[dup] hQ1 /[swap] _ /[swap] /[apply] heq
    move: hQ1=> /[swap] /[apply] /[apply]
    sby srw heq=> {}heq > /heq }
  { move=> > /evalExact_sat ![>] /[dup] hQ1 /[swap] _ /[swap] /[apply] heq
    move: hQ1=> /[swap] /[apply] /[apply]
    sby srw heq=> {}heq > /heq }
  { sby move=> > _ ih > /ih }
  { sby unfold purepost }
  { sby unfold purepost }
  { move=> > /evalExact_sat ![>] /[dup] hQ₁ /[swap] /[apply] ? ih1 ih2 >
    move: hQ₁=> /[dup] hQ₁ /ih1 {}ih1
    scase: (finite_state (s' ∪ w_1))=> p /non_mem_union []
    move=> /[dup] /insert_same hins ? /[dup] /hins {}hins
    move: hQ₁=> /ih2 /[apply] /== {}ih2
    srw [1](insert_delete_id s' p)=> //
    sby move=> /ih2 /hins }
  { sdone }
  { move=> > _ ? > /= [] _ []
    sby srw insert_mem_keys }
  { move=> > _ /evalExact_sat ![>] /[dup] hQ₁ /[swap] _ /[swap] /[apply] ?
    sby move: hQ₁=> /[swap] /[apply] ih > /ih }
  { move=> > ? _ ih >
    scase: (finite_state' n.natAbs (sa ∪ s'))
    move=> p [] /ih /== {}ih /Finmap.disjoint_union_left /[dup] hdisj [] /ih {}ih
    move=> /union_difference_id heq
    srw -[1]heq=> /ih
    srw [2]Finmap.union_comm_of_disjoint ; rotate_left
    { sby srw Finmap.Disjoint.symm_iff }
    sby move: hdisj=> [] /[swap] /union_same_keys /[apply] }
  { sby move=> > _ ih > /ih }
  move=> > /evalExact_sat ![>] /[dup] hQ1 /[swap] _ /[swap] /[apply] heq
  move: hQ1=> /[swap] /[apply] /[apply]
  sby srw heq=> {}heq > /heq

local instance : HWand (hProp) (heap → Prop) hProp where
  hWand := hwand


/- ----------------------------- Frame Rule ----------------------------- -/

abbrev tohProp (h : heap -> Prop) : hProp := h
abbrev ofhProp (h : val -> hProp) : val -> heap -> Prop := h

lemma frame_eq_rw :
  s.Disjoint h2 →
  (fun v' s' ↦ v' = v ∧ s' = s ∪ h2) =
  (qstar (fun v' s' ↦ v' = v ∧ s' = s) (tohProp (fun h ↦ h = h2))) := by
  move=> ? ; funext=> /==
  apply Iff.intro
  { move=> [] *
    exists s, h2 }
  unfold tohProp
  sby move=> ![] >

lemma evalExact_frame_val (v : val) (s h2 : state) :
  s.Disjoint h2 →
  evalExact (s ∪ h2) t (fun v' s' ↦ v' = v ∧ s' = s ∪ h2) →
  evalExact (s ∪ h2) t
    (qstar (fun v' s' ↦ v' = v ∧ s' = s) (tohProp (fun h ↦ h = h2))) := by
  move=> ?
  sby srw frame_eq_rw

lemma purepost_frame :
  s.Disjoint h2 →
  (purepost (s ∪ h2) P) =
  (qstar (purepost s P) (tohProp fun h ↦ h = h2)) := by
  move=> ?
  unfold purepost tohProp
  funext=> /==
  apply Iff.intro
  { move=> [] *
    exists s, h2 }
  sby move=> ![>]

lemma evalExact_frame_unop_binop :
  s.Disjoint h2 →
  evalExact (s ∪ h2) t (purepost (s ∪ h2) P) →
  evalExact (s ∪ h2) t (qstar (purepost s P) (tohProp fun h ↦ h = h2)) := by
  move=> ?
  sby srw purepost_frame

lemma read_state_frame :
  s.Disjoint h2 →
  p ∈ s →
  (fun v' s' ↦ v' = read_state p (s ∪ h2) ∧ s' = s ∪ h2 ) =
  (qstar (fun v' s' ↦ v' = read_state p s ∧ s' = s) (tohProp fun h ↦ h = h2)) := by
  move=> ??
  unfold tohProp
  funext=> /==
  apply Iff.intro
  { sby srw in_read_union_l }
  srw in_read_union_l
  sby move=> ![>]

lemma evalExact_frame_get :
  s.Disjoint h2 →
  p ∈ s →
  evalExact (s ∪ h2) t (fun v' s' ↦ v' = read_state p (s ∪ h2) ∧ s' = s ∪ h2 ) →
  evalExact (s ∪ h2) t
    (qstar (fun v' s' ↦ v' = read_state p s ∧ s' = s) (tohProp fun h ↦ h = h2)) := by
  move=> ??
  sby srw read_state_frame

lemma insert_frame :
  s.Disjoint h2 →
  p ∈ s →
  fun v'' s' ↦ v'' = val_unit ∧ s' = Finmap.insert p v' (s ∪ h2) =
  (qstar (fun v'' s' ↦ v'' = val_unit ∧ s' = Finmap.insert p v' s) (tohProp fun h ↦ h = h2)) := by
  move=> ??
  unfold tohProp
  funext=> /==
  apply Iff.intro
  { srw Finmap.insert_union
    move=> [] *
    exists Finmap.insert p v' s, h2=> /== ⟨|⟩ // ⟨|⟩
    sby apply disjoint_insert_l }
  move=> ![>] /== [] [] [] ? [] /==
  sby srw Finmap.insert_union

lemma evalExact_frame_set :
  s.Disjoint h2 →
  p ∈ s →
  evalExact (s ∪ h2) t
    (fun v'' s' ↦ v'' = val_unit ∧ s' = Finmap.insert p v' (s ∪ h2)) →
  evalExact (s ∪ h2) t
    (qstar (fun v'' s' ↦ v'' = val_unit ∧ s' = Finmap.insert p v' s) (tohProp fun h ↦ h = h2)) := by
  move=> ??
  sby srw insert_frame

lemma evalExact_frame (h1 h2 : state) t (Q : val → hProp) :
  evalExact h1 t (ofhProp Q) →
  Finmap.Disjoint h1 h2 →
  evalExact (h1 ∪ h2) t (Q ∗ (tohProp (fun h ↦ h = h2))) :=
by
  simp [ofhProp]
  move=> /== heval
  elim: heval h2
  { move=> > *
    sby apply evalExact_frame_val }
  { move=> > *
    sby apply evalExact_frame_val }
  { move=> > *
    sby apply evalExact_frame_val }
  { move=> ???????? ih1 ?? /ih1 ? ; constructor=>//
    sby move=> ?? ![] }
  { move=> ???????? ih1 ?? /ih1 ? ; apply evalExact.app_arg2=>//
    sby move=> ?? ![] }
  { sby move=> * ; apply evalExact.app_fun }
  { sby move=> * ; apply evalExact.app_fix }
  { move=> ??????? ih1 ih2 ? /ih1 ? ; apply evalExact.seq=>//
    move=> ? s2 ![??? hQ2 *] ; subst s2 hQ2
    sby apply ih2 }
  { move=> ???????? ih1 ih2 ? /ih1 ? ; apply evalExact.let=>//
    move=> ?? ![??? hQ2 ? hU] ; subst hU hQ2
    sby apply ih2}
  { sby move=> * }
  { move=> > ? > *
    apply evalExact_frame_unop_binop=> //
    sby apply evalExact.unop }
  { move=> > ? > *
    apply evalExact_frame_unop_binop=> //
    sby apply evalExact.binop }
  { move=> > ; unfold tohProp
    move=> _ _ ih1 ih2 > /ih1 {}ih1
    apply evalExact.ref
    { apply ih1 }
    move=> {ih1} > ![>] hQ₁ /= -> ? -> p ?
    have eqn:(p ∉ w) := by sdone
    have eqn':((w.insert p v1).Disjoint h2) := by sby apply disjoint_update_not_r
    move: hQ₁ eqn eqn'=> /ih2 /[apply] /[apply] {ih2}
    srw insert_union=> // hq
    apply evalExact_post_eq ; rotate_left ; apply hq
    apply funext=> v ; apply funext=> h ; apply propext=> ⟨|⟩
    { move=> ![>] /= ? -> ? ->
      exists (w_2.erase p), h2=> ⟨//|/==⟩ ⟨|⟩
      apply erase_disjoint=> //
      sby srw remove_not_in_r }
    move=> ![>] /= ? -> ?
    scase: [p ∈ h]
    { move=> ? ; srw erase_of_non_mem=> // []
      exists w_2, h2=> /== ⟨|⟩ //
      sby srw erase_of_non_mem }
    move=> /Finmap.mem_iff [v'] /reinsert_erase_union heq herase
    srw (heq w_2 h2)=> // {heq}
    exists (w_2.insert p v'), h2=> /== ⟨|⟩
    { srw -insert_delete_id=> //
      have eqn:(p ∉ h.erase p) := by apply Finmap.not_mem_erase_self
      move: eqn
      sby srw herase }
    sby apply disjoint_update_not_r }
  { move=> > ? > *
    apply evalExact_frame_get=> //
    sby apply evalExact.get }
  { move=> > [] ? > * * ;
    apply evalExact_frame_set=> //
    sby apply evalExact.set }
  -- { move=> * ; apply eval.eval_free=>//
  --   srw remove_disjoint_union_l ; apply hstar_intro=>//
  --   sby apply disjoint_remove_l }
  { move=> > ??? ih1 ih2 > /ih1 {ih1} ?
    apply evalExact.alloc_arg=> // >
    sby move=> ![>] }
  { unfold tohProp=> > ?? ih > ? ; apply evalExact.alloc=> // >
    move=> /ih /[apply] {}ih /Finmap.disjoint_union_left [] /[dup] /ih {}ih ?
    srw Finmap.Disjoint.symm_iff -Finmap.union_assoc=> ?
    have eqn:((sb ∪ sa).Disjoint h2) := by
      sby srw Finmap.disjoint_union_left
    apply ih in eqn=> {ih} hq ; apply evalExact_post_eq ; rotate_left ; apply hq
    apply funext=> v ; apply funext=> h ; apply propext=> ⟨|⟩
    { move=> ![>] /= ? -> ? ->
      exists (w \ sb), h2=> /== ⟨|⟩ // ⟨|⟩
      { sby apply disjoint_disjoint_diff }
      apply union_diff_disjoint_r
      sby apply Finmap.Disjoint.symm }
    move=> ![>] /= ? -> ? /[dup] heq
    have eqn:((w ∪ h2).Disjoint sb) := by
      { srw -heq ; unfold Finmap.Disjoint=> /== }
    move: eqn=> /Finmap.disjoint_union_left [ ? _]
    move=> /(union_monotone_r (intersect h sb))
    srw diff_insert_intersect_id Finmap.union_assoc [2]Finmap.union_comm_of_disjoint
    rotate_left
    { apply Finmap.Disjoint.symm ; sby apply disjoint_intersect_r }
    srw -Finmap.union_assoc=> ?
    exists (w ∪ intersect h sb), h2=> //== ⟨|⟩
    { sby srw intersect_disjoint_cancel }
    constructor=> //
    srw Finmap.disjoint_union_left ; constructor=> //
    sby apply disjoint_intersect_r }
  { move=> // }
  move=> > ?? ih₁ ih₂ ??; econstructor
  { apply ih₁=> // }
  sby move=> > ![]

lemma eval_frame (h1 h2 : state) t (Q : val -> hProp) :
  eval h1 t (ofhProp Q) →
  Finmap.Disjoint h1 h2 →
  eval (h1 ∪ h2) t (Q ∗ (tohProp (fun h ↦ h = h2))) :=
by
  unfold ofhProp tohProp; elim=> //
  { move=> > ?? _ ih' *; apply eval.eval_app_arg1=> //
    move=> > ![] ?? ? -> ? ->; aesop }
  { move=> *; apply eval.eval_app_arg2=> //
    move=> > ![] ?? ? -> ? ->; aesop }
  { move=> *; apply eval.eval_app_fun=> // }
  { move=> *; apply eval.eval_app_fix=> // }
  { move=> *; apply eval.eval_seq=> //
    move=> > ![] ?? ? -> ? ->; aesop }
  { move=> *; apply eval.eval_let=> //
    move=> > ![] ?? ? -> ? ->; aesop }
  { move=> > ? Pp *; apply eval.eval_unop=> //
    move=> ? /Pp ?; exists s, h2 }
  { move=> > ? Pp *; apply eval.eval_binop=> //
    move=> ? /Pp ?; exists s, h2 }
  { move=> > ? _ dj ih' ?
    constructor; apply dj=> //
    move=> > ![] s1 ? ? -> dj' -> p /== ??
    rw [@Finmap.insert_union]
    apply eval_conseq; apply ih'=> //
    { sby apply disjoint_update_not_r s1 h2 p v1 dj' }
    move=> v s /= ![] h ? /== ? -> ? ->
    rw [remove_not_in_r h h2 p]=> //
    exists (h.erase p), h2=> ⟨|⟩//⟨|⟩//⟨|⟩//
    sby apply erase_disjoint h h2 p }
  { move=> > *; apply eval.eval_get
    simp; aesop; exists s, h2=> ⟨|⟩//
    sby rw [in_read_union_l s h2 p] }
  { move=> > *; apply eval.eval_set=> //
    exists (Finmap.insert p v' s), h2=> ⟨|⟩// ⟨|⟩// ⟨|⟩
    { apply disjoint_insert_l s h2 p v'=> // }
    rw [@Finmap.insert_union] }
  { move=> *; apply eval.eval_alloc_arg=> //
    move=> > ![] ??? -> ? ->; aesop }
  { move=> > ? ih ih' dj
    apply eval.eval_alloc=> // > ?? dj';
    srw -Finmap.union_assoc; apply eval_conseq; apply ih'=> //
    { move: dj'; sby rw [@Finmap.disjoint_union_left] }
    { move: dj'; srw ?Finmap.disjoint_union_left /===> ? ? ⟨|⟩//
      sby apply (Finmap.Disjoint.symm h2 sb) }
    move=> > /= ? /= ![] s ? /= ? -> ? ->
    exists (s \ sb), h2=> ⟨|⟩//⟨|⟩//⟨|⟩
    { sby apply disjoint_disjoint_diff s h2 sb }
    apply union_diff_disjoint_r=> //
    move: dj'; sby rw [@Finmap.disjoint_union_left] }
  move=> *; constructor=> // ?? ![] ??? -> ? ->; aesop

-- previous free proof

  -- { move=> > ; unfold tohProp
  --   move=> > ?? hin hfree ih1 ih2 > /ih1 {}ih1
  --   apply eval.eval_ref
  --   { apply ih1 }
  --   { move=> > ![>] hQ₁ *
  --     subst s₂
  --     have eqn:(p ∉ w) := by sdone
  --     have eqn':((w.insert p v).Disjoint w_1) := by sby apply disjoint_update_not_r
  --     move: hQ₁ eqn eqn'=> /ih2 /[apply] /[apply]
  --     sby srw insert_union }
  --   { sby move=> > ![>] /hin }
  --   move=> > ![>] /[dup] /hin ? /hfree hQ_1 /= [] ? []
  --   exists (w.erase p), h2=> /== ⟨|⟩ // ⟨|⟩
  --   apply erase_disjoint=> //
  --   sby apply remove_disjoint_union_l }

end evalProp


/- --------------------- Structural Rules --------------------- -/

/- For proofs below, [admit] takes the place of [xsimp] -/

/- Consequence and Frame Rule -/

lemma triple_conseq t H' Q' H Q :
  triple t H' Q' →
  H ==> H'→
  Q' ===> Q →
  triple t H Q :=
by
  move=> /triple *
  srw triple => ??
  sby apply (eval_conseq _ _ Q' _)

lemma triple_frame t H (Q : val -> hProp) H' :
  triple t H Q →
  triple t (H ∗ H') (Q ∗ H') :=
by
  move=> /triple hEval
  srw triple=>? ![?? hs ? hDisj hU] ; srw hU
  apply eval_conseq
  { apply (eval_frame _ _ _ _ (hEval _ hs) hDisj) =>// }
  { move=> ?
    sby srw ?qstarE ; xsimp }


/- Extraction Rules -/

lemma triple_hpure t P H Q :
  (P → triple t H Q) →
  triple t (⌜P⌝ ∗ H) Q :=
by
  move=> ?
  srw triple=> ? ![?? [? /hempty_inv hEmp] ?? hU]
  sby srw hU hEmp Finmap.empty_union

lemma triple_hexists t A (J : A → hProp) Q :
  (forall x, triple t (J x) Q) →
  triple t (hexists J) Q :=
by
  sby srw []triple => hJ ? [] ? /hJ

lemma triple_hforall t A (x : A) (J : A → hProp) Q:
  triple t (J x) Q →
  triple t (hforall J) Q :=
by
  move=> /triple_conseq ; sapply => ?
  sapply ; sdone

lemma triple_hwand_hpure_l t (P : Prop) H Q :
  P →
  triple t H Q →
  triple t (⌜P⌝ -∗ H) Q :=
by
  move=> ? /triple_conseq ; sapply
  rw [hwand_hpure_l] <;> sdone
  sby move=> ??

/- A useful corollary of [triple_hpure] -/
lemma triple_hpure' t (P : Prop) Q :
  (P → triple t emp Q) →
  triple t ⌜P⌝ Q :=
by
  move=> /triple_hpure
  sby srw hstar_hempty_r

/- Heap -naming rule -/
lemma triple_named_heap t H Q :
  (forall h, H h → triple t (fun h' ↦ h' = h) Q) →
  triple t H Q :=
by
  sby move=> hH ? /hH

/- Combined and ramified rules -/

lemma triple_conseq_frame H2 H1 Q1 t H Q :
  triple t H1 Q1 →
  H ==> H1 ∗ H2 →
  Q1 ∗ H2 ===> Q →
  triple t H Q :=
by
  move=> /triple_frame hFra /triple_conseq hCons /hCons
  sapply ; apply hFra

lemma triple_ramified_frame H1 Q1 t H Q :
  triple t H1 Q1 →
  H ==> H1 ∗ (Q1 -∗ Q) →
  triple t H Q :=
by
  move=> ??;
  apply triple_conseq_frame=>//
  sby srw -qwand_equiv=> ?


/- ---------------------- Rules for Terms ---------------------- -/

lemma triple_eval_like t1 t2 H Q :
  eval_like t1 t2 →
  triple t1 H Q →
  triple t2 H Q :=
by
  srw eval_like=> hLike ? ??
  sby apply hLike

lemma triple_val v H Q :
  H ==> Q v →
  triple (trm_val v) H Q :=
by
  move=> ? ??
  sby apply eval.eval_val

lemma triple_val_minimal v :
  triple (trm_val v) emp (fun r ↦ ⌜r = v⌝) :=
by
  apply triple_val
  xsimp

lemma triple_fun x t1 H Q :
  H ==> Q (val_fun x t1) →
  triple (trm_fun x t1) H Q :=
by
  move=> ? ??
  sby apply eval.eval_fun

lemma triple_fix f x t1 H Q :
  H ==> Q (val_fix f x t1) →
  triple (trm_fix f x t1) H Q :=
by
  move=> ? ??
  sby apply eval.eval_fix

lemma triple_seq t1 t2 H Q H1 :
  triple t1 H (fun _ ↦ H1) →
  triple t2 H1 Q →
  triple (trm_seq t1 t2) H Q :=
by
  srw triple=> hH ? ??
  apply eval.eval_seq
  { sby apply hH }
  sdone

lemma triple_let x t1 t2 Q1 H Q :
  triple t1 H Q1 →
  (forall v1, triple (subst x v1 t2) (Q1 v1) Q) →
  triple (trm_let x t1 t2) H Q :=
by
  srw triple=> hH ? ??
  apply eval.eval_let
  { sby apply hH }
  sdone

lemma triple_let_val x v1 t2 H Q :
  triple (subst x v1 t2) H Q →
  triple (trm_let x v1 t2) H Q :=
by
  move=> ?
  apply triple_let _ _ _ (fun v ↦ ⌜v = v1⌝ ∗ H)
  { apply triple_val ; xsimp }
  move=> ?
  sby apply triple_hpure

-- WIP
/- wp (trm_ref x (val_int n) t) Q =
   (p ~~> n) -* wp (subst x t) (Q * ∃ʰ n, (p ~~> n)) -/
lemma triple_ref (v : val) :
  (forall (p : loc), triple (subst x p t2) (H ∗ (p ~~> v)) (Q ∗ ∃ʰ v, p ~~> v)) →
  triple (trm_ref x (trm_val v) t2) H Q :=
by
  move=> htriple h ?
  apply eval.eval_ref
  { sby apply (eval.eval_val h v (fun v' h' ↦ v' = v ∧ h' = h)) }
  move=> > [->->] > ?
  move: (htriple p)=> /triple_conseq {}htriple
  have eqn:(triple (subst x p t2) (H ∗ p ~~> v) fun v s ↦ Q v (s.erase p)) := by
    apply htriple=> //
    move=> > h /= ![>] ? /hexists_inv [v'] /hsingl_inv ->
    sby move=> /union_singleton_eq_erase /[apply] <-
  move=> {htriple}
  apply eqn
  exists h, Finmap.singleton p v
  move=> ⟨//|⟩ ⟨|⟩
  apply hsingle_intro=> ⟨|⟩
  apply disjoint_single=>//
  sby apply insert_eq_union_single=> //

lemma triple_if (b : Bool) t1 t2 H Q :
  triple (if b then t1 else t2) H Q →
  triple (trm_if b t1 t2) H Q :=
by
  move=> ? ??
  sby apply eval.eval_if

lemma triple_app_fun x v1 v2 t1 H Q :
  v1 = val_fun x t1 →
  triple (subst x v2 t1) H Q →
  triple (trm_app v1 v2) H Q :=
by
  move=> * ??
  sby apply eval.eval_app_fun

lemma triple_app_fun_direct x v2 t1 H Q :
  triple (subst x v2 t1) H Q →
  triple (trm_app (val_fun x t1) v2) H Q :=
by
  move=> ?
  sby apply triple_app_fun

lemma triple_app_fix v1 v2 f x t1 H Q :
  v1 = val_fix f x t1 →
  triple (subst x v2 (subst f v1 t1)) H Q →
  triple (trm_app v1 v2) H Q :=
by
  move=> * ??
  sby apply eval.eval_app_fix

lemma triple_app_fix_direct v2 f x t1 H Q :
  f ≠ x →
  triple (subst x v2 (subst f (val_fix f x t1) t1)) H Q →
  triple (trm_app (val_fix f x t1) v2) H Q :=
by
  move=> * ??
  sby apply triple_app_fix


/- Rules for Heap-Manipulating Primitive Operations -/

lemma read_state_single p v :
  read_state p (Finmap.singleton p v) = v :=
by
  srw read_state Finmap.lookup_singleton_eq

lemma triple_get v (p : loc) :
  triple (trm_app val_get p)
    (p ~~> v)
    (fun r ↦ ⌜r = v⌝ ∗ (p ~~> v)) :=
by
  move=> ? []
  apply eval.eval_get=>//
  srw hstar_hpure_l => ⟨|⟩ //
  apply read_state_single

lemma triple_set w p (v : val) :
  triple (trm_app val_set (val_loc p) v)
    (p ~~> w)
    (fun r ↦ ⌜r = val_unit⌝ ∗ (p ~~> v)) :=
by
  move=> ? []
  apply eval.eval_set=>//
  sby srw Finmap.insert_singleton_eq hstar_hpure_l

-- lemma triple_free' p v :
--   triple (trm_app val_free (val_loc p))
--     (p ~~> v)
--     (fun r ↦ ⌜r = val_unit⌝) :=
-- by
--   move=> ? []
--   apply eval.eval_free=>//
--   srw hpure hexists hempty
--   exists rfl
--   apply Finmap.ext_lookup => ?
--   sby srw Finmap.lookup_empty Finmap.lookup_eq_none Finmap.mem_erase

-- lemma triple_free p v:
--   triple (trm_app val_free (val_loc p))
--     (p ~~> v)
--     (fun _ ↦ emp) :=
-- by
--   apply (triple_conseq _ _ _ _ _ (triple_free' p v))
--   { sdone }
--   xsimp ; xsimp

/- Rules for Other Primitive Operations -/

lemma triple_unop op v1 (P : val → Prop) :
  evalunop op v1 P →
  triple (trm_app op v1) emp (fun r ↦ ⌜P r⌝) :=
by
  move=> ? ? []
  apply (eval_conseq _ _ (fun v s ↦ P v ∧ s = ∅))
  { apply eval.eval_unop=>//
    sby srw purepostin }
  { move=> ?? [] ? hEmp
    sby srw hEmp }

lemma triple_binop op v1 v2 (P : val → Prop) :
  evalbinop op v1 v2 P →
  triple (trm_app op v1 v2) emp (fun r ↦ ⌜P r⌝) :=
by
  move=> ? ? []
  apply (eval_conseq _ _ (fun v s ↦ P v ∧ s = ∅))
  { apply eval.eval_binop=>//
    sby srw purepostin }
  { move=> ?? [] ? hEmp
    sby srw hEmp }

lemma triple_add n1 n2 :
  triple (trm_app val_add (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_int (n1 + n2)⌝) :=
by
  sby apply triple_binop

lemma triple_addr r1 r2 :
  triple (trm_app val_add (val_real r1) (val_real r2))
    emp
    (fun r ↦ ⌜r = val_real (r1 + r2)⌝) :=
by
  sby apply triple_binop

lemma triple_div n1 n2 :
  n2 ≠ 0 →
  triple (trm_app val_div (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_int (n1 / n2)⌝) :=
by
  move=> ?
  sby apply triple_binop

lemma triple_divr r1 r2 :
  r2 ≠ 0 →
  triple (trm_app val_div (val_real r1) (val_real r2))
    emp
    (fun r ↦ ⌜r = val_real (r1 / r2)⌝) :=
by move=> ?; sby apply triple_binop

-- lemma triple_rand n :
--   n > 0 →
--   triple (trm_app val_rand (val_int n))
--     emp
--     (fun r ↦ ⌜exists n1, r = val_int n1 ∧ 0 <= n1 ∧ n1 < n⌝) :=
-- by
--   move=> ?
--   sby apply triple_unop

lemma triple_neg (b1 : Bool) :
  triple (trm_app val_neg b1)
    emp
    (fun r ↦ ⌜r = val_bool (¬b1)⌝) :=
by
  sby apply triple_unop

lemma triple_opp n1 :
  triple (trm_app val_opp (val_int n1))
    emp
    (fun r ↦ ⌜r = val_int (-n1)⌝) :=
by
  sby apply triple_unop

lemma triple_oppr r1 :
  triple (trm_app val_opp (val_real r1))
    emp
    (fun r ↦ ⌜r = val_real (-r1)⌝) :=
by sby apply triple_unop

lemma triple_eq v1 v2 :
  triple (trm_app val_eq (trm_val v1) (trm_val v2))
    emp
    (fun r ↦ ⌜r = is_true (v1 = v2)⌝) :=
by
  sby apply triple_binop

lemma triple_neq v1 v2 :
  triple (trm_app val_neq (trm_val v1) (trm_val v2))
    emp
    (fun r ↦ ⌜r = is_true (v1 ≠ v2)⌝) :=
by
  sby apply triple_binop

lemma triple_sub n1 n2 :
  triple (trm_app val_sub (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_int (n1 - n2)⌝):=
by
  sby apply triple_binop

lemma triple_subr r1 r2 :
  triple (trm_app val_sub (val_real r1) (val_real r2))
    emp
    (fun r ↦ ⌜r = val_real (r1 - r2)⌝):=
by sby apply triple_binop

lemma triple_mul n1 n2 :
  triple (trm_app val_mul (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_int (n1 * n2)⌝):=
by
  sby apply triple_binop

lemma triple_mulr r1 r2 :
  triple (trm_app val_mul (val_real r1) (val_real r2))
    emp
    (fun r ↦ ⌜r = val_real (r1 * r2)⌝):= by
  sby apply triple_binop

lemma triple_mod n1 n2 :
  n2 ≠ 0 →
  triple (trm_app val_mod (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_int (n1 % n2)⌝) :=
by
  move=> ?
  sby apply triple_binop

lemma triple_le n1 n2 :
  triple (trm_app val_le (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_bool (n1 <= n2)⌝) :=
by
  sby apply triple_binop

lemma triple_ler r1 r2 :
  triple (trm_app val_le (val_real r1) (val_real r2))
    emp
    (fun r ↦ ⌜r = val_bool (r1 <= r2)⌝) :=
by sby apply triple_binop

lemma triple_lt n1 n2 :
  triple (trm_app val_lt (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_bool (n1 < n2)⌝) :=
by
  sby apply triple_binop

lemma triple_ltr r1 r2 :
  triple (trm_app val_lt (val_real r1) (val_real r2))
    emp
    (fun r ↦ ⌜r = val_bool (r1 < r2)⌝) :=
by sby apply triple_binop

lemma triple_ge n1 n2 :
  triple (trm_app val_ge (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_bool (n1 >= n2)⌝) :=
by
  sby apply triple_binop

lemma triple_ger r1 r2 :
  triple (trm_app val_ge (val_real r1) (val_real r2))
    emp
    (fun r ↦ ⌜r = val_bool (r1 >= r2)⌝) :=
by sby apply triple_binop

lemma triple_gt n1 n2 :
  triple (trm_app val_gt (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_bool (n1 > n2)⌝) :=
by
  sby apply triple_binop

lemma triple_gtr r1 r2 :
  triple (trm_app val_gt (val_real r1) (val_real r2))
    emp
    (fun r ↦ ⌜r = val_bool (r1 > r2)⌝) :=
by sby apply triple_binop

private lemma abs_nonneg' n :
  n ≥ 0 → Int.natAbs n = n :=
by
  move=> ?
  sby elim: n

lemma triple_ptr_add (p : loc) (n : ℤ) :
  p + n >= 0 →
  triple (trm_app val_ptr_add p n)
    emp
    (fun r ↦ ⌜r = val_loc ((p + n).natAbs)⌝) :=
by
  move=> ?
  apply triple_binop
  apply evalbinop.evalbinop_ptr_add
  sby srw abs_nonneg

lemma triple_ptr_add_nat p (f : ℕ) :
  triple (trm_app val_ptr_add (val_loc p) (val_int (Int.ofNat f)))
    emp
    (fun r ↦ ⌜r = val_loc (p + f)⌝) :=
by
  apply triple_conseq _ _ _ _ _ (triple_ptr_add p f _)=>// ? /=
  sby xsimp

/- ============== Definitions for Arrays ============== -/

def hheader (n : Int) (p : loc) : hProp :=
  p ~~> (val_int n)

lemma hheader_eq p n :
  (hheader n p) = (p ~~> (val_int n)) := by
  sdone

def hcell (v : val) (p : loc) (i : Int) : hProp :=
  ((p + 1 + (Int.natAbs i)) ~~> v) ∗ ⌜i >= 0⌝

lemma hcell_eq v p i :
  (hcell v p i) = ((p + 1 + (Int.natAbs i)) ~~> v) ∗ ⌜i >= 0⌝ := by
  sdone

lemma hcell_nonneg v p i :
  hcell v p i ==> hcell v p i ∗ ⌜i >= 0⌝ := by
  sby srw hcell_eq ; xsimp

def hseg (L : List val) (p : loc) (j : Int) : hProp :=
  match L with
  | []      => emp
  | x :: L' => (hcell x p j) ∗ (hseg L' p (j + 1))

def harray (L : List val) (p : loc) : hProp :=
  hheader (L.length) p ∗ hseg L p 0

lemma harray_eq p L :
  harray L p = ∃ʰ n, ⌜n = L.length⌝ ∗ hheader n p ∗ hseg L p 0 := by
  sby srw harray ; xsimp[L.length]; xsimp=> //

/- inversion lemma for hseg -/

lemma hseg_start_eq L p j1 j2 :
  j1 = j2 →
  hseg L p j1 ==> hseg L p j2 := by
  sdone


/- ================== Implementation of Arrays ================= -/

/- A simplified specification for non-negative pointer addition -/

lemma natabs_nonneg (p : Nat) (n : Int) :
  n ≥ 0 → (p + n).natAbs = p + n.natAbs := by
  omega

lemma triple_ptr_add_nonneg (p : loc) (n : Int) :
  n >= 0 →
  triple [lang| p ++ n]
    emp
    (fun r ↦ ⌜r = val_loc (p + Int.natAbs n)⌝) := by
  move=> ?
  apply (triple_conseq _ emp
    (fun r ↦ ⌜r = val_loc (Int.toNat (Int.natAbs (p + n)))⌝))
  apply triple_ptr_add
  { omega }
  { xsimp }
  xsimp ; xsimp=> /==
  sby apply natabs_nonneg


/- Semantics of Low-Level Block Allocation -/

-- #check eval.eval_alloc
/- eval.eval_alloc {x : var} {t2 : trm} (sa : state) (n : ℤ) (Q : val → state → Prop) :
  n ≥ 0 →
    (∀ (p : loc) (sb : state),
        sb = conseq (make_list n.natAbs val_uninit) p →
          p ≠ null →
          Finmap.Disjoint sa sb → eval (sb ∪ sa)
            (subst x p t2) fun v s ↦ Q v (s \ sb)) →
      eval sa (trm_alloc x ([lang| n]) t2) Q
 -/

/- Heap predicate for describing a range of cells -/

def hrange (L : List val) (p : loc) : hProp :=
  match L with
  | []      => emp
  | x :: L' => (p ~~> x) ∗ (hrange L' (p + 1))

lemma hrange_intro L p :
  (hrange L p) (conseq L p) := by
  induction L generalizing p ; srw conseq hrange=> //
  apply hstar_intro=>//
  sby apply disjoint_single_conseq

lemma triple_alloc_arg :
  ¬trm_is_val t1 →
  triple t1 H Q1 →
  (∀ v, triple (trm_alloc x (trm_val v) t2) (Q1 v) Q ) →
  triple (trm_alloc x t1 t2) H Q := by
  unfold triple=> ? hs ? > /hs ?
  sby apply eval.eval_alloc_arg

-- #check triple_ref

lemma int_eq_sub (l m n : ℤ) :
  l + m = n → l = n - m := by omega

lemma list_inc_natabs {α : Type} (L : List α) :
  ((L.length : ℤ) + 1).natAbs = (L.length : ℤ).natAbs + 1 := by
  omega

lemma hrange_eq_conseq (L : List val) (n : ℤ) (p : loc) (s : state) :
  L.length = n →
  hrange L p s →
  s.keys = (conseq (make_list n.natAbs val_uninit) p).keys := by
  elim: L n p s=> > ; unfold hrange
  { sby move=> /= <- /= /hempty_inv -> }
  move=> ih > /== /[dup] /int_eq_sub /[dup] hn /ih {}ih  <-
  srw -hn at ih
  move: ih=> /= ih {hn}
  unfold hrange=> ![>] /hsingl_inv ? /ih {}ih ? ->
  unfold conseq make_list
  srw list_inc_natabs=> /== >
  move: ih
  sby srw ?Finset.ext_iff Finmap.mem_keys=> ?

lemma triple_alloc (n : Int) :
  n ≥ 0 →
  (∀ (p : loc), triple (subst x p t)
    (H ∗ ⌜p ≠ null⌝ ∗ hrange (make_list n.natAbs val_uninit) p)
    (Q ∗ ⌜p ≠ null⌝  ∗ ∃ʰ L, ⌜L.length = n⌝ ∗ hrange L p) ) →
  triple (trm_alloc x n t) H Q := by
  move=> ? htriple h ?
  apply eval.eval_alloc=> // > *
  move: (htriple p)=> /triple_conseq {}htriple
  specialize (htriple (H ∗ ⌜p ≠ null⌝ ∗ hrange (make_list n.natAbs val_uninit) p))
  specialize (htriple (fun v s ↦ Q v (s \ sb)))
  have eqn:(triple (subst x p t)
    (H ∗ ⌜p ≠ null⌝ ∗ hrange (make_list n.natAbs val_uninit) p)
    fun v s ↦ Q v (s \ sb)) := by
    { apply htriple=> // {htriple}
      move=> > s ![>] ? ![>] /hpure_inv [] _ ->
      move=> /hexists_inv [L] ![>] /hpure_inv [] ? -> ? _
      move=> /== -> _ -> ? ->
      srw diff_disjoint_eq=> //
      subst sb ; sby apply hrange_eq_conseq }
  move=> {htriple}
  apply eqn
  exists h, sb=> ⟨//|⟩ ⟨|⟩
  { exists ∅, sb => ⟨//|/==⟩ ⟨|⟩
    subst sb ; apply hrange_intro
    sdone }
  constructor=> //
  sby srw Finmap.union_comm_of_disjoint Finmap.Disjoint.symm_iff


/- --------------------- Strongest Post Condition --------------------- -/

abbrev sP h t :=fun v => h∀ (Q : val -> hProp), ⌜eval h t Q⌝ -∗ Q v

open Classical

noncomputable def sP' (h : heap) (t : trm) : (val → hProp) :=
  if ex : ∃ Q, evalExact h t Q then choose ex else fun _ _ ↦ False

lemma sP'_strongest :
  eval h t Q → sP' h t ===> Q := by
  move=>  /evalExact_post hex
  unfold sP'
  scase: [∃ Q, evalExact h t Q]
  { move=> > ; sby srw dif_neg=> // ?? }
  move=> > ; srw (dif_pos h_1)=> //
  sby apply choose_spec in h_1=> /hex

lemma evalExact_sP' :
  evalExact h t Q → evalExact h t (sP' h t) := by
  move=> ?
  have hex:(∃ Q, evalExact h t Q) := by exists Q
  unfold sP'
  scase: [∃ Q, evalExact h t Q]=> // >
  srw (dif_pos hex)
  apply choose_spec

-- lemma sP'_post :
--   eval h t Q → eval h t (sP' h t) := by
--   sby move=> /eval_imp_exact=> [>] /evalExact_sP' /exact_imp_eval

-- lemma sP'_post_exact :
--   eval h t Q → evalExact h t (sP' h t) := by
--   sby move=> /eval_imp_exact [>] /evalExact_sP'

lemma hpure_intr :
  (P -> H s) -> (⌜P⌝ -∗ H) s := by
  move=> ?
  scase: [P]=> p
  { exists ⊤, s, ∅; repeat' constructor=> //
    { xsimp=>// }
    exact Finmap.Disjoint.symm ∅ s (Finmap.disjoint_empty s) }
  exists H=> /=
  exists s, ∅=> ⟨|⟨|⟨|⟩⟩⟩ //
  { move=> ⟨|⟩//; xsimp }
  exact Finmap.Disjoint.symm ∅ s (Finmap.disjoint_empty s)

lemma hforall_impl (J₁ J₂ : α -> hProp) :
  (forall x, J₁ x ==> J₂ x) ->
  hforall J₁ ==> hforall J₂ := by
  move=> ? h /[swap]  x/(_ x)//

lemma sP_strongest :
  eval h t Q -> sP h t ===> Q := by
  move=> ev v; unfold sP;
  apply himpl_hforall_l _ Q
  srw hwand_hpure_l=> //;
