import SPLean.Common.State

import SPLean.Theories.XSimp
import SPLean.Theories.XChange
import SPLean.Common.Util
import SPLean.Theories.SepLog
import SPLean.Theories.WP1
import SPLean.Theories.Lang


open val trm prim
open Theories

/- Syntax for array operations -/

-- set_option pp.notation false
-- #check [lang|
--   let arr := mkarr 5 1 in
--   arr[4] := 2 ;
--   arr[3]
--   ]

/- ==================== Properties of Arrays ==================== -/

/- Implementing absolute value operator -/

lemma nonneg_eq_abs (n : Int) :
  0 ≤ n → n.natAbs = n := by omega

lemma neg_mul_abs (n : Int) :
  n < 0 → -1 * n = n.natAbs := by omega

attribute [-simp] Int.natCast_natAbs

lemma triple_abs (i : Int) :
  triple [lang| val_abs i]
    emp
    (fun r ↦ ⌜r = val_int i.natAbs⌝) := by
  xstep triple_lt
  xstep triple_sub
  xstep triple_mul
  xif=> /== ?
  { xval ; xsimp
    congr!; omega }
  xval ; xsimp
  sby srw nonneg_eq_abs


/- properties of [hseg] -/

lemma hseg_nil p j :
  hseg [] p j = emp := by
  sdone

lemma hseg_one v p j :
  hseg (v :: []) p j = hcell v p j := by
  sby srw hseg hseg ; xsimp

lemma hseg_cons v p j L :
  hseg (v :: L) p j = hcell v p j ∗ hseg L p (j + 1) := by
  sby srw hseg

lemma hseg_app L1 L2 p j :
  hseg (L1 ++ L2) p j =
  hseg L1 p j ∗ hseg L2 p (j + L1.length) := by
  induction L1 generalizing j with
  | nil         => srw hseg /== ; hsimp
  | cons _ _ ih =>
      sby dsimp ; srw ?hseg_cons ih -[4](add_comm 1) add_assoc ; hsimp


/- ------------------- Focus lemmas for [hseg] ------------------- -/

lemma list_cons_length (A : Type) (x : A) (L : List A) :
  (x :: L).length = 1 + L.length := by
  simp
  omega

lemma list_nil_length (A : Type) :
  ([] : List A).length = 0 := by sdone

lemma ofnat_plusone (n : Nat) :
  Int.ofNat (n + 1) = (Int.ofNat n) + 1 := by sdone


lemma list_middle_inv (A : Type) (n : Nat) (l : List A) :
  n < l.length →
  exists (x : A) (l1 l2 : List A),
    l = l1 ++ x :: l2 ∧ l1.length = n := by
  induction n generalizing l with
  | zero       => move=> ? ; cases l => //
  | succ n' ih =>
      move=> hlen ; cases l with
      | nil => sdone
      | cons x l' =>
          have h : (n' < l'.length) := by srw list_cons_length at hlen ; omega
          apply ih in h=> [x' [l1 [l2]]] ?
          exists x', (x :: l1), l2 ; sdone

lemma nth_app_r {A : Type} (_ : Inhabited A) n (l1 l2 : List A) :
  n ≥ l1.length →
  (l1 ++ l2)[n]! = l2[n - l1.length]! := by
  elim: l1 n l2
  { sdone }
  sby move=> > ? []

-- #check List.getElem_of_append
lemma nth_middle (A : Type) (IA : Inhabited A) (n : Nat)
  (l1 l2 : List A) (x : A) :
  n = l1.length → (l1 ++ x :: l2)[n]! = x := by
  move=> ?
  sby srw nth_app_r

lemma cons_app {A : Type} (l1 l2 : List A) (x : A) :
  x :: l1 ++ l2 = x :: (l1 ++ l2) := by
  sdone

lemma update_app_r {A : Type} (l1 l2 : List A) n v :
  n ≥ l1.length →
  (l1 ++ l2).set n v = l1 ++ l2.set (n - l1.length) v := by
  elim: l1 l2 n v
  { sdone }
  move=> > ? >
  sby cases n

-- #check List.concat_eq_append
lemma update_middle (A : Type) (_ : Inhabited A) (n : Nat)
  (l1 l2 : List A) (x v : A) :
  n = l1.length → (l1 ++ x :: l2).set n v = (l1.concat v) ++ l2 := by
  move=> ? ; subst n=> /==

-- set_option pp.explicit true
-- set_option pp.all true
lemma hseg_focus_relative (k : Nat) L p j (v : 0 <= k ∧ k < L.length):
  hseg L p j ==>
  hcell L[k]! p (j + k)
    ∗ (h∀ w, hcell w p (j + k) -∗ hseg (L.set k w) p j) := by
  move: v=> [] ? /list_middle_inv ![> ?] hlen
  move: (Eq.symm hlen) => /nth_middle hmid
  subst L ; srw (hmid _ w_2 w) hseg_app hseg_cons hlen -hstar_comm_assoc
  apply himpl_frame_r
  apply himpl_hforall_r => ?
  move: (Eq.symm hlen) => /(update_middle val _ k w_1 w_2 w) hset
  srw hset ?List.concat_append ?hseg_app ?hseg_cons ?hlen
  { sby xsimp }
  sdone

lemma add_Int.natAbs i j :
  0 <= i - j → j + Int.natAbs (i - j) = i := by omega

-- set_option pp.all true
lemma hseg_focus (i j : Int) L p (v : 0 <= i - j ∧ i - j < L.length) :
  0 <= i - j ∧ i - j < L.length →
  hseg L p j ==>
  hcell L[(i - j).natAbs]! p i
    ∗ (h∀ w, hcell w p i -∗ hseg (L.set (i - j).natAbs w) p j) := by
  move=> [] * ; xchange (hseg_focus_relative (i - j).natAbs) ; omega
  srw add_Int.natAbs ; xsimp ; omega

lemma harray_focus i L p (v : 0 <= i ∧ i < L.length) :
  0 <= i ∧ i < L.length →
  harray L p ==>
  hcell L[Int.natAbs i]! p i
    ∗ (h∀ w, hcell w p i -∗ harray (L.set (Int.natAbs i) w) p) := by
  move:v => [] *
  -- move=> [] *
  srw ?harray ; xchange (hseg_focus i) ; simp; omega=> //==
  apply himpl_frame_r ; apply himpl_hforall_r => x
  xchange (hforall_specialize _ x)
  xsimp

lemma set_nth_same (A : Type) (IA : Inhabited A) (n : Nat) (l : List A) :
  n < l.length → l.set n l[n]! = l := by
  elim: l n;
  { sdone }
  move=> >? ; scase
  all_goals sdone

lemma harray_focus_read i L p :
  0 <= i ∧ i < L.length →
  harray L p ==>
  hcell L[Int.natAbs i]! p i ∗ (hcell L[Int.natAbs i]! p i -∗ harray L p) := by
  move=> [] *
  xchange (harray_focus i L p) => // ; xsimp
  xchange (hforall_specialize _ L[Int.natAbs i]!)
  srw set_nth_same
  xsimp
  omega


/- ========================= Triple rules for Arrays ========================= -/

open eval

set_option linter.hashCommand false
#hint_xapp triple_get
#hint_xapp triple_set

lemma triple_array_length_hheader (n : Int) (p : loc) :
  triple (trm_app val_array_length p)
    (hheader n p)
    (fun r ↦ ⌜r = n⌝ ∗ hheader n p) := by
    xwp
    srw hheader
    xapp

-- set_option pp.all true

lemma triple_array_get_hcell (p : loc) (i : Int) (v : val) :
  triple [lang| val_array_get p i]
    (hcell v p i)
    (fun r ↦ ⌜r = v⌝ ∗ hcell v p i) := by
    /- trm_apps val_array_get [p, i] -/
    xwp
    unfold hcell
    xpull=> ?
    xapp triple_ptr_add_nonneg
    xwp
    xapp triple_ptr_add_nonneg
    sby xapp; xsimp

lemma triple_array_set_hcell (p : loc) (i : Int) (v w : val) :
  triple (trm_app val_array_set p i v)
    (hcell w p i)
    (fun _ ↦ hcell v p i) := by
    xwp
    srw hcell
    xpull=> ?
    xapp triple_ptr_add_nonneg
    xwp
    xapp triple_ptr_add_nonneg
    sby unfold hcell ; xapp ; xsimp

lemma triple_array_get_hseg L (p : loc) (i j : Int) (_ : 0 <= i - j ∧ i - j < L.length) :
  triple [lang| val_array_get p i]
    (hseg L p j)
    (fun r ↦ ⌜r = L[(i - j).natAbs]!⌝ ∗ hseg L p j) := by
    xtriple
    xchange (hseg_focus i)=>//
    xapp triple_array_get_hcell
    xchange hforall_specialize
    rw [<- nonneg_eq_abs (i - j)] => /=
    xsimp=> //
    srw set_nth_same // ; omega

lemma triple_array_set_hseg L (p : loc) (i j : Int) (v : val) :
  0 <= i - j ∧ i - j < L.length →
  triple (trm_app val_array_set p i v)
    (hseg L p j)
    (fun _ ↦ hseg (L.set (Int.natAbs (i - j)) v) p j) := by
    move=> ?
    xtriple
    xchange (hseg_focus i)=>//
    xapp triple_array_set_hcell
    xchange hforall_specialize

lemma hseg_eq_hrange L p (k : Nat) :
  hseg L p k = hrange L (p + 1 + k) := by
  elim: L p k
  { sdone }
  move=> > ih >
  srw hrange hseg [2]add_assoc -ih hcell /==
  xsimp
  sby srw -hstar_assoc ; xsimp

lemma of_nat_nat n :
  OfNat.ofNat n = n := by sdone

lemma nat_abs_succ (n : Int) :
  n ≥ 0 → (n + 1).natAbs = n.natAbs + 1 := by omega

-- lemma triple_array_fill (n : Int) L (p : loc) (i : Int) (v : val) :
--   n = L.length →
--   triple (trm_app val_array_fill p i n v)
--     (hseg L p i)
--     (fun _ ↦ hseg (make_list n.natAbs v) p i) := by
--   scase: n=> >
--   { elim: a L p i v=> > /== ih > ; xwp
--     { xapp triple_gt ; xwp
--       xif=> ? //
--       xwp ; xval
--       unfold make_list
--       have h : L = [] := by
--         apply List.eq_nil_of_length_eq_zero ; omega
--       srw h ; sdone }
--     move=> ? ; xwp
--     xapp triple_gt ; xwp
--     xif=> /== ; xwp
--     xapp triple_array_set_hseg=> //== ; any_goals omega
--     scase: L
--     { move=> /== ? ; omega }
--     move=> /== >? ; xwp
--     xapp triple_sub=> /== ; xwp
--     xapp triple_add ;  xtriple
--     srw nat_abs_succ //==
--     srw make_list ?hseg_cons
--     xapp ih ; xsimp }
--   sdone

lemma make_list_len (n : Int) (v : val) :
  (make_list n.natAbs v).length = n.natAbs := by
  elim: n=> >
  { elim: a=> > //
    move=> ?
    sby srw make_list }
  elim: a=> > //
  move=> ? /=
  sby srw make_list

-- lemma triple_array_make_hseg (n : Int) (v : val) :
--   n >= 0 →
--   triple (trm_app val_array_make n v)
--     emp
--     (funloc p ↦ hheader n.natAbs p ∗ hseg (make_list (n.natAbs) v) p 0) := by
--   xwp
--   xapp triple_add ; xwp
--   xapp triple_alloc=> > ; xwp
--   rw [nat_abs_succ, make_list, hrange]
--   srw ?of_nat_nat //== ; any_goals omega
--   xapp ; xwp
--   srw -hheader_eq -(hseg_eq_hrange (make_list n.natAbs val_uninit) p 0)
--   xapp triple_array_fill ; xwp
--   { xval ; xsimp => //
--     apply himpl_of_eq
--     sby srw nonneg_eq_abs }
--   srw make_list_len
--   omega

lemma triple_array_get L (p : loc) (i : Int) : --(v : 0 <= i ∧ i < L.length) :
   0 <= i ∧ i < L.length →
   triple (trm_app val_array_get p i)
    (harray L p)
    (fun r ↦ ⌜r = L[i.natAbs]!⌝ ∗ harray L p) := by
  xtriple
  srw harray ; xapp triple_array_get_hseg => /==
  xsimp

lemma triple_array_set L (p : loc) (i : Int) (v : val) :
  0 <= i ∧ i < L.length →
  triple (trm_app val_array_set p i v)
    (harray L p)
    (fun _ ↦ harray (L.set (Int.natAbs i) v) p) := by
  move=> ?
  xtriple
  srw ?harray ; xapp triple_array_set_hseg => /==
  xsimp

lemma triple_array_length L (p : loc) :
  triple (trm_app val_array_length p)
    (harray L p)
    (fun r ↦ ⌜r = val_int L.length⌝ ∗ harray L p) := by
    xtriple
    srw harray
    xapp triple_array_length_hheader
    xsimp

-- lemma triple_array_make (n : Int) (v : val) :
--   n ≥ 0 →
--   triple (trm_app val_array_make n v)
--     emp
--     (funloc p ↦ harray (make_list n.natAbs v) p) := by
--   move=> ?
--   xtriple
--   srw harray
--   xapp triple_array_make_hseg=> >
--   xsimp
--   { sdone }
--   sby srw make_list_len nonneg_eq_abs


/- Rules for [default_get] and [default_set] -/

-- instance : GetElem (List val) Int val (fun L i => 0 <= i ∧ i < L.length) where
--     getElem vs i h := vs.get ⟨i.natAbs, by cases i <;> sdone⟩
--      := vs.getD i.natAbs default
-- `a[I]`,  `a.[I]`\/ `a[I].`

instance: GetElem (List α) Int α (fun L i => i.natAbs < L.length) :=
  ⟨fun xs i _ => xs[i.natAbs]⟩

example (L : List val) (i : Int) (_ : i.natAbs < L.length) :
  L[i.natAbs]! = L[i]! := by
  rfl

example (L : List Int) (i : Int) (_ : i.natAbs < L.length) :
  L[i.natAbs]! = L[i]! := by
  rfl

lemma int_index_eq {_ : Inhabited α} (L : List α) (i : Int) :
  L[i.natAbs]! = L[i]! := by
  rfl

lemma natabs_eq (a : Nat) :
  a = (Int.ofNat a).natAbs := by rfl

-- set_option pp.all true
lemma get_out_of_bounds {_ : Inhabited α} (L : List α) (i : Int) :
  L.length ≤ i.natAbs →
  L[i]! = default := by
  srw -int_index_eq
  elim: L i
  { sdone }
  move=> > ih >
  scase: i
  { move=> /= >
    elim: a => >?
    sdone
    move=> /==
    sby srw (natabs_eq n)=> /ih }
  move=> /== >
  sby srw (natabs_eq a) => /ih

lemma set_keep_length (L : List val) i v :
  L.length = (L.set i v).length := by
  elim: L ; all_goals sdone

lemma set_out_of_bounds (L : List val) i v :
  i < 0 ∨ i ≥ L.length →
  L.set i v = L := by
  move=> [] ?
  { elim: L ; all_goals sdone }
  elim:L i ; sdone
  move=> > ? > ?
  scase: i ; all_goals sdone

-- set_option pp.all true
-- lemma triple_array_default_set L (p : loc) (i : Int) (v : val) :
--   triple [lang| p[i] := v]
--     (harray L p)
--     (fun _ ↦ harray (L.set (i.natAbs) v) p) := by
--     xwp
--     xapp triple_abs ; xwp
--     xapp triple_array_length ; xwp
--     xapp triple_lt ; xwp
--     xif=> /== lh
--     { xapp triple_array_set }
--     xwp; xval
--     sby srw List.set_eq_of_length_le

/- Rules and definitions for integer arrays -/

lemma getElem!_nil_intint (n : Int) :
  ([] : List Int)[n]! = default := by sdone

lemma getElem!_nil_intval (n : Int) :
  ([] : List val)[n]! = default := by sdone

def harray_int (L : List Int) : loc → hProp :=
  harray (L.map val_int)

-- set_option maxHeartbeats 400000
-- lemma triple_array_default_get_int (p : loc) (i : Int) (L : List Int) :
--   triple [lang| p[i]]
--     (harray_int L p)
--     (fun r ↦ ⌜r = L[i]!⌝ ∗ harray_int L p) := by
--   unfold harray_int
--   xwp
--   xapp triple_abs ; xwp
--   xapp triple_array_length ; xwp
--   xapp triple_lt ; xwp
--   xif=> /==
--   srw -(List.length_map L val_int)=> ?
--   { xapp triple_array_get; xsimp
--     srw ?getElem!_pos ?getElem?_pos // }
--   xwp; xval; xsimp
--   sby srw get_out_of_bounds
