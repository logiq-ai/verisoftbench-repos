import Lean.Elab.Tactic
import Qq

import SPLean.Theories.HProp
import SPLean.Common.Util


-- open hprop_scope
open Lean Lean.Expr Lean.Meta Qq
open Lean Elab Command Term Meta Tactic

/- **============ `hsimp` trivrial goal simplification tactic ============** -/

lemma himpl_of_eq H1 H2 : H1 = H2 -> H1 ==> H2 :=
  by sby move=>-> ?

/- Hack to solve `H ==> H` automatically. What is a better way?  -/
@[simp]
lemma himpl_refl_resolve  H : (H ==> H) = True := by
  sby simp=> ?

-- lemma himpl_hstar_trans_l H1 H2 H3 H4 :
--   H1 ==> H2 ->
--   H2 ∗ H3 ==> H4 ->
--   H1 ∗ H3 ==> H4 := by
--   move=> ??
--   eapply himpl_trans=> //
--   apply himpl_frame_lr=> //

lemma qimpl_refl (Q : α -> hProp) : Q ===> Q := by
  sby move=> ?; apply himpl_refl

/- Hack to solve `Q ===> Q` automatically. What is a better way?  -/
@[simp]
lemma qimpl_refl_resolve (Q : α -> hProp) : (Q ===> Q) = True := by
  sby simp=> ??


lemma hstar_comm_assoc (H1 H2 H3 : hProp) :
  H1 ∗ H2 ∗ H3 = H2 ∗ H1 ∗ H3 := by
  sby srw -hstar_assoc [2]hstar_comm hstar_assoc

@[simp]
lemma star_post_empty (Q : α -> hProp) :
  Q ∗ emp = Q := by
  move=> !?; srw qstarE hstar_hempty_r


attribute [heapSimp] hstar_hempty_l hstar_hempty_r
                     hstar_assoc star_post_empty hwand_hempty_l

@[heapSimp]
lemma foo : (@OfNat.ofNat ℕ n _) = (n : ℤ) := rfl
@[heapSimp]
lemma foo' : (@OfNat.ofNat ℤ n _) = (n : ℤ) := rfl
@[heapSimp]
lemma foo'' : (@OfNat.ofNat val n _) = val.val_int (n : ℤ) := by congr
-- @[heapSimp]
lemma foo''' (n : ℕ) : (@OfNat.ofNat ℕ n _) = n := rfl


macro "hsimp" : tactic => `(tactic| (simp only [heapSimp]; try dsimp))


/- **============ `xsimp` implementation ============** -/

def XSimp (hl hr : hProp × hProp × hProp) :=
  let (hla, hlw, hlt) := hl
  let (hra, hrg, hrt) := hr
  hla ∗ hlw ∗ hlt ==> hra ∗ hrg ∗ hrt

@[heapSimp]
def protect (x : α) := x

structure XSimpR where
  hla : Term
  hlw : Term
  hlt : Term
  ----------
  hra : Term
  hrg : Term
  hrt : Term

def getGoalStxNN : Lean.Elab.Tactic.TacticM Syntax := do
  delabNoNotations $ <- getMainTarget

/-
XSimp
      (@Prod.mk hProp (Prod hProp hProp)
        (@HStar.hStar hProp hProp $_ H1 (@HStar.hStar hProp hProp $_ H2 (@HStar.hStar hProp hProp $_ H3 (@HStar.hStar hProp hProp $_ (Q true) (@HStar.hStar hProp hProp $_ (@HWand.hWand hProp hProp $_ (hpure P) HX) (@HStar.hStar hProp hProp $_ HY hempty))))))
        (@Prod.mk hProp hProp Hlw Hlt))
      (@Prod.mk hProp (Prod hProp hProp) Hra (@Prod.mk hProp hProp Hrg Hrt))
-/

def XSimpRIni : TacticM XSimpR := withMainContext do
  (<- getMainGoal).setTag `xsimp_goal
  let goal <- getGoalStxNN
  let `(XSimp $hl $hr) := goal | throwError "not a XSimp goal"
  let `(@Prod.mk hProp $_ $hla $hlwt) := hl | throwError "not a XSimp goal"
  let `(@Prod.mk hProp hProp $hlw $hlt) := hlwt | throwError "not a XSimp goal"
  let `(@Prod.mk hProp $_ $hra $hrgt) := hr | throwError "not a XSimp goal"
  let `(@Prod.mk hProp hProp $hrg $hrt) := hrgt | throwError "not a XSimp goal"
  return { hla := hla, hlw := hlw, hlt := hlt, hra := hra, hrg := hrg, hrt := hrt }


/- ------------ Tactic for flipping an interated [∗] operation ------------ -/

lemma hstar_flip_0 :
  emp = emp := by
  sdone

lemma hstar_flip_1 :
  h1 ∗ emp = h1 ∗ emp := by
  sdone

lemma hstar_flip_2 :
  h1 ∗ h2 ∗ emp = h2 ∗ h1 ∗ emp := by
  srw hstar_comm_assoc

lemma hstar_flip_3 :
  h1 ∗ h2 ∗ h3 ∗ emp = h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hstar_flip_2 !(hstar_comm_assoc h3)

lemma hstar_flip_4 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ emp = h4 ∗ h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hstar_flip_3 !(hstar_comm_assoc h4)

lemma hstar_flip_5 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ emp = h5 ∗ h4 ∗ h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hstar_flip_4 !(hstar_comm_assoc h5)

lemma hstar_flip_6 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ emp =
  h6 ∗ h5 ∗ h4 ∗ h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hstar_flip_5 !(hstar_comm_assoc h6)

lemma hstar_flip_7 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ emp =
  h7 ∗ h6 ∗ h5 ∗ h4 ∗ h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hstar_flip_6 !(hstar_comm_assoc h7)

lemma hstar_flip_8 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ emp =
  h8 ∗ h7 ∗ h6 ∗ h5 ∗ h4 ∗ h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hstar_flip_7 !(hstar_comm_assoc h8)

lemma hstar_flip_9 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ emp =
  h9 ∗ h8 ∗ h7 ∗ h6 ∗ h5 ∗ h4 ∗ h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hstar_flip_8 !(hstar_comm_assoc h9)

lemma hstar_flip_10 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ h10 ∗ emp =
  h10 ∗ h9 ∗ h8 ∗ h7 ∗ h6 ∗ h5 ∗ h4 ∗ h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hstar_flip_9 !(hstar_comm_assoc h10)

def hstar_flip_lemma (i : Nat) : Ident :=
  mkIdent s!"hstar_flip_{i}".toName

partial def hstar_arity (hs : Term) : TacticM Nat :=
  match hs with
  | `(hempty)      => return (0)
  | `(@HStar.hStar hProp hProp $_ $_ $_ $h2) => do
      let n <- hstar_arity h2
      return (1 + n)
  | _           => throwError "cannot get arity"

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

elab "hstar_flip" h:term : tactic => do
  let i <- hstar_arity h
  {| eapply $(hstar_flip_lemma i) |}

lemma xsimp_flip_acc_l_lemma :
  hla = hla' →
  XSimp (hla', emp, emp) (hra, hrg, emp) →
  XSimp (hla, emp, emp) (hra, hrg, emp) := by
  sby move=> h /h

lemma xsimp_flip_acc_r_lemma :
  hra = hra' →
  XSimp (hla, emp, emp) (hra', hrg, emp) →
  XSimp (hla, emp, emp) (hra, hrg, emp) := by
  sby move=> h /h

elab "xsimp_flip_acc_l" hla:term : tactic =>
  {| eapply xsimp_flip_acc_l_lemma ; hstar_flip $hla |}

elab "xsimp_flip_acc_r" hra:term : tactic =>
  {| eapply xsimp_flip_acc_r_lemma ; hstar_flip $hra |}

def xsimp_flip_acc_lr (hla hra : Term) : TacticM Unit :=
  {| xsimp_flip_acc_l $hla ; xsimp_flip_acc_r $hra |}


/- ------------ Tactic for picking a particular heap proposition ------------ -/

/- TODO: Pregenerate such lemmas automatically -/
/- Note: Copilot can generate them pretty good -/
lemma hstar_pick_1 :
  h1 ∗ h = h1 ∗ h := by
  sdone

lemma hstar_pick_2  :
  h1 ∗ h2 ∗ h = h2 ∗ h1 ∗ h := by
  sby srw hstar_comm_assoc

lemma hstar_pick_3 :
  h1 ∗ h2 ∗ h3 ∗ h = h3 ∗ h1 ∗ h2 ∗ h := by
  sby srw (hstar_comm_assoc h2); apply hstar_pick_2

lemma hstar_pick_4 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h = h4 ∗ h1 ∗ h2 ∗ h3 ∗ h := by
  sby srw (hstar_comm_assoc h3); apply hstar_pick_3

lemma hstar_pick_5 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h = h5 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h := by
  sby srw (hstar_comm_assoc h4); apply hstar_pick_4

lemma hstar_pick_6 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h = h6 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h := by
  sby srw (hstar_comm_assoc h5); apply hstar_pick_5

lemma hstar_pick_7 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h = h7 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h := by
  sby srw (hstar_comm_assoc h6); apply hstar_pick_6

lemma hstar_pick_8 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h = h8 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h := by
  sby srw (hstar_comm_assoc h7); apply hstar_pick_7

lemma hstar_pick_9 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ h = h9 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h := by
  sby srw (hstar_comm_assoc h8); apply hstar_pick_8

lemma hstar_pick_10 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ h10 ∗ h = h10 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ h := by
  sby srw (hstar_comm_assoc h9); apply hstar_pick_9

lemma hstar_pick_last_1 :
  h1 = h1 := by sdone

lemma hstar_pick_last_2 :
  h1 ∗ h2 = h2 ∗ h1 := by
  sby srw hstar_comm

lemma hstar_pick_last_3 :
  h1 ∗ h2 ∗ h3 = h3 ∗ h1 ∗ h2 := by
  sby srw (hstar_comm h2); apply hstar_pick_2

lemma hstar_pick_last_4 :
  h1 ∗ h2 ∗ h3 ∗ h4 = h4 ∗ h1 ∗ h2 ∗ h3 := by
  sby srw (hstar_comm h3); apply hstar_pick_3

lemma hstar_pick_last_5 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 = h5 ∗ h1 ∗ h2 ∗ h3 ∗ h4 := by
  sby srw (hstar_comm h4); apply hstar_pick_4

lemma hstar_pick_last_6 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 = h6 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 := by
  sby srw (hstar_comm h5); apply hstar_pick_5

lemma hstar_pick_last_7 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 = h7 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 := by
  sby srw (hstar_comm h6); apply hstar_pick_6

lemma hstar_pick_last_8 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 = h8 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 := by
  sby srw (hstar_comm h7); apply hstar_pick_7

lemma hstar_pick_last_9 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 = h9 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 := by
  sby srw (hstar_comm h8); apply hstar_pick_8

lemma hstar_pick_last_10 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ h10 = h10 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 := by
  sby srw (hstar_comm h9); apply hstar_pick_9

def hstar_pick_lemma (i : Nat) (pickLast : Bool) : Ident :=
  if pickLast then
    mkIdent s!"hstar_pick_last_{i}".toName
  else
    mkIdent s!"hstar_pick_{i}".toName

lemma xsimp_pick_lemma :
  hla2 = hla1 ->
  XSimp (hla1, hlw, hlt) hr ->
  XSimp (hla2, hlw, hlt) hr := by sby move=>->

def xsimp_pick (i : Nat) (last? : Bool) : TacticM Unit :=
   {| apply xsimp_pick_lemma
      · apply $(hstar_pick_lemma i last?) |}

partial def hstar_search (hs : Term) (test : Nat -> Term -> optParam Bool false -> TacticM Unit) :=
  let rec loop (i : Nat) (hs : Term)  : TacticM Unit := do
    match hs with
    | `(@HStar.hStar hProp hProp $_ $_ $h1 $h2) => do
      try
        test i h1
      catch _ => loop (i+1) h2
    | _ => test i hs true
  loop 1 hs

def xsimp_pick_same (h hla : Term) (f : optParam (Nat → Bool → TacticM Unit) xsimp_pick) : TacticM Unit := do
  let h  <- Tactic.elabTerm h none
  hstar_search hla fun i h' last? => do
    let h' <- Tactic.elabTerm h' none
    let .true <-
      withAssignableSyntheticOpaque <| isDefEq h' h | throwError "not equal"
    f i last?

def xsimp_pick_applied (h hla : Term) : TacticM Unit := do
  let h <- Term.elabTerm h  none
  hstar_search hla fun i h' last? => do
    let h' <- Term.elabTerm h' none
    let numArgs + 1 := h'.getAppNumArgs' | throwError "not equal"
    let h' := h'.consumeMData.getAppPrefix numArgs
    let .true <-
      withAssignableSyntheticOpaque <| isDefEq h h' | throwError "not equal"
    xsimp_pick i last?


/- ============ Theory for `xsimp` ============ -/
lemma xsimp_start_lemma :
  XSimp (emp, emp, h1 ∗ emp) (emp, emp, h2 ∗ emp) ->
  h1 ==> h2 := by
  sby srw XSimp ; hsimp

/- ----- Cancellation tactic for proving [xsimp] lemmas ----- -/

lemma hstars_simp_start_lemma :
  H1 ∗ emp ==> emp ∗ H2 ∗ emp →
  H1 ==> H2 := by
  sby hsimp

lemma hstars_simp_keep_lemma :
  H1 ==> (H ∗ Ha) ∗ Ht →
  H1 ==> Ha ∗ H ∗ Ht := by
  sby hsimp ; srw hstar_comm_assoc

lemma hstars_simp_cancel_lemma :
  H1 ==> Ha ∗ Ht →
  H ∗ H1 ==> Ha ∗ H ∗ Ht := by
  srw hstar_comm_assoc=> ?
  sby apply himpl_frame_lr

lemma hstars_simp_pick_lemma :
  H1 = H1' →
  H1' ==> H2 →
  H1 ==> H2 := by
  sby move=> h /h

def hstars_simp_pick (i : Nat) (_ : Bool) : TacticM Unit :=
  let L := hstar_pick_lemma i false
  {| eapply hstars_simp_pick_lemma ; apply $(L) |}

def hstars_simp_start : TacticM Unit := withMainContext do
  let goal <- getGoalStxNN
  match goal with
  | `(himpl $_ $_) =>
      {| apply hstars_simp_start_lemma ; try srw ?hstar_assoc |}
  | _          => throwError "hstars_simp_start failure"

def hstars_simp_step : TacticM Unit := withMainContext do
  let goal <- getGoalStxNN
  match goal with
    | `(himpl $Hl $Hr) =>
        match Hr with
          | `(@HStar.hStar hProp hProp $_ $_ $_ $hs) =>
              match hs with
              | `(@HStar.hStar hProp hProp $_ $_ $H $_) =>
                    try
                      xsimp_pick_same H Hl hstars_simp_pick ;
                      {| apply hstars_simp_cancel_lemma |}
                    catch ex =>
                      let s <- ex.toMessageData.toString
                      if s == "not equal" then
                        {| apply hstars_simp_keep_lemma |}
                      else
                        throw ex
              | _ => throwError "cannot simplify"
          | _ => throwError "cannot simplify"
    | _ => throwError "cannot simplify"

def hstars_simp_post :=
  {| hsimp ; try apply himpl_refl |}

elab "hstars_simp_start" : tactic => do
  hstars_simp_start

elab "hstars_simp_step" : tactic => do
  hstars_simp_step

elab "hstars_simp" : tactic => do
  hstars_simp_start ;
  {| repeat hstars_simp_step |} ;
  hstars_simp_post


/- ------------ Lemmas for LHS step ------------ -/

macro "xsimp_l_start" : tactic =>
  `(tactic| (srw ?XSimp=> ? ; try hsimp))

macro "xsimp_l_start'" : tactic =>
  `(tactic| (xsimp_l_start ; apply himpl_trans=>// ; hstars_simp ; try hstars_simp))

lemma xsimp_l_hempty :
  XSimp (hla, hlw, hlt) hr ->
  XSimp (hla, hlw, emp ∗ hlt) hr := by
  sby hsimp

lemma xsimp_l_hpure :
  (p -> XSimp (hla, hlw, hlt) hr) ->
  XSimp (hla, hlw, ⌜p⌝ ∗ hlt) hr := by
  xsimp_l_start
  rw [hstar_pick_3]
  sby apply himpl_hstar_hpure_l

lemma xsimp_l_acc_wand :
  XSimp (hla, h ∗ hlw, hlt) hr ->
  XSimp (hla, hlw, h ∗ hlt) hr := by
  xsimp_l_start'

lemma xsimp_l_acc_other :
  XSimp (h ∗ hla, hlw, hlt) hr ->
  XSimp (hla, hlw, h ∗ hlt) hr := by
  xsimp_l_start'

lemma xsimp_l_hexists :
  (∀ x, XSimp (hla, hlw, j x ∗ hlt) hr) ->
  XSimp (hla, hlw, (hexists j) ∗ hlt) hr := by
  srw ?XSimp=> H
  rw [hstar_pick_3, hstar_hexists]
  apply himpl_hexists_l=> x
  rw [<- hstar_pick_3]
  apply H

lemma xsimp_l_cancel_hwand_hempty :
  XSimp (hla, hlw, h ∗ hlt) hr ->
  XSimp (hla, (emp -∗ h) ∗ hlw, hlt) hr := by

  xsimp_l_start'

lemma xsimpl_l_cancel_hwand_hstar_hempty :
  XSimp (Hla, Hlw, ((H2 -∗ H3) ∗ Hlt)) HR ->
  XSimp (Hla, (((emp ∗ H2) -∗ H3) ∗ Hlw), Hlt) HR := by
  xsimp_l_start'

lemma xsimp_l_keep_wand :
  XSimp (H ∗ Hla, Hlw, Hlt) HR →
  XSimp (Hla, H ∗ Hlw, Hlt) HR := by
  xsimp_l_start'

lemma xsimp_l_hwand_reorder :
  h1 = h1' ->
  XSimp (hla, ((h1' -∗ h2) ∗ hlw), hlt) hr ->
  XSimp (hla, (h1 -∗ h2) ∗ hlw, hlt) hr := by
  sby move=> H /H

/-
  XSimp (hla, (h1 ∗ h2 ∗ ... ∗ hn -∗ h) ∗ hlw, hlt) hr
-/
lemma xsimp_l_cancel_hwand_hstar :
  XSimp (Hla, Hlw, (H2 -∗ H3) ∗ Hlt) HR →
  XSimp ((H1 ∗ Hla), (((H1 ∗ H2) -∗ H3) ∗ Hlw), Hlt) HR := by
  -- srw ?XSimp
  -- hsimp
  xsimp_l_start'
  srw hwand_curry_eq
  apply hwand_cancel

lemma xsimp_l_cancel_hwand :
  XSimp (emp, Hlw, Hla ∗ H2 ∗ Hlt) HR →
  XSimp ((H1 ∗ Hla), ((H1 -∗ H2) ∗ Hlw), Hlt) HR := by
  xsimp_l_start'
  apply hwand_cancel

lemma xsimp_l_cancel_qwand α (Q1 Q2 : α -> hProp) x :
  XSimp (emp, Hlw, (Hla ∗ Q2 x ∗ Hlt)) HR ->
  XSimp ((Q1 x ∗ Hla), ((Q1 -∗ Q2) ∗ Hlw), Hlt) HR := by
  xsimp_l_start'
  srw hstar_comm
  apply (himpl_hstar_trans_l) ; apply (qwand_specialize _ x)
  srw hstar_comm ; apply hwand_cancel

lemma xpull_protect (h : H1 ==> protect H2) : H1 ==> H2 :=
  by simp [protect] at h; assumption

/- ------------ Lemmas for RHS step ------------ -/

lemma xsimp_r_hempty :
  XSimp hl (hra, hrg, hrt) ->
  XSimp hl (hra, hrg, emp ∗ hrt) := by
  sby srw hstar_hempty_l

lemma xsimp_r_hwand_same :
  XSimp hl (hra, hrg, hrt) ->
  XSimp hl (hra, hrg, (h -∗ h) ∗ hrt) := by
  xsimp_l_start'
  sby srw hwand_equiv ; hsimp

lemma xsimp_r_hpure :
  XSimp hl (hra, hrg, hrt) -> p ->
  XSimp hl (hra, hrg, hpure p ∗ hrt) := by
  move=> ? ; xsimp_l_start'
  sby apply himpl_hempty_hpure

lemma xsimp_r_hexists α (x : α) hl hra hrg hrt j :
  XSimp hl (hra, hrg, j x ∗ hrt) ->
  XSimp hl (hra, hrg, (hexists j) ∗ hrt) := by
  xsimp_l_start'
  apply himpl_hexists_r
  sdone

lemma xsimp_r_keep :
  XSimp hl (h ∗ hra, hrg, hrt) ->
  XSimp hl (hra, hrg, h ∗ hrt) := by
  xsimp_l_start'

lemma xsimpl_r_hgc_or_htop :
  XSimp HL (Hra, (H ∗ Hrg), Hrt) ->
  XSimp HL (Hra, Hrg, (H ∗ Hrt)) := by
  xsimp_l_start'

lemma xsimpl_r_htop_drop :
  XSimp HL (Hra, Hrg, Hrt) ->
  XSimp HL (Hra, Hrg, (⊤ ∗ Hrt)) := by
  xsimp_l_start'
  apply himpl_htop_r

/- ------------ Lemmas for LHS/RHS step ------------ -/

macro "xsimp_lr_start" : tactic =>
  `(tactic| (srw ?XSimp ; try hsimp))

macro "xsimp_lr_start'" : tactic =>
  `(tactic| (xsimp_l_start ; try hsimp ; try (apply himp_trans=>// ; hstars_simp)))

lemma xsimp_lr_hwand_hfalse :
  XSimp (Hla, emp, emp) ((⌜False⌝ -∗ H1) ∗ emp, emp, emp) := by
  xsimp_lr_start
  srw hwand_equiv
  sby apply himpl_hstar_hpure_l

lemma xsimp_lr_cancel_same :
  XSimp (hla, hlw, hlt) (hra, hrg, hrt) ->
  XSimp (h ∗ hla, hlw, hlt) (hra, hrg, h ∗ hrt) := by
  xsimp_lr_start'
  srw [2]hstar_pick_3
  sby apply himpl_frame_r

lemma himpl_lr_refl :
  XSimp (hla, emp, emp) (hla, emp, emp) := by
  xsimp_l_start'

lemma xsimp_lr_hwand :
  XSimp (emp, emp, (H1 ∗ Hla)) (emp, emp, H2 ∗ emp) ->
  XSimp (Hla, emp, emp) ((H1 -∗ H2) ∗ emp, emp, emp) := by
  srw ?XSimp ; hsimp
  sby srw hwand_equiv

lemma xsimpl_lr_qwand α (Q1 Q2 : α -> hProp) :
  (forall x, XSimp (emp, emp, (Q1 x ∗ Hla)) (emp, emp, (Q2 x ∗ emp))) ->
  XSimp (Hla, emp, emp) (((Q1 -∗ Q2) ∗ emp), emp, emp) := by
  xsimp_lr_start
  srw qwand_equiv=> ??
  srw qstarE
  sdone

lemma xsimpl_lr_qwand_unit (Q1 Q2 : Unit -> hProp) :
  XSimp (emp, emp, (Q1 ( ) ∗ Hla)) (emp, emp, (Q2 ( ) ∗ emp)) ->
  XSimp (Hla, emp, emp) ((Q1 -∗ Q2) ∗ emp, emp, emp) := by
  move=> ?
  sby apply xsimpl_lr_qwand=> ?

lemma himpl_lr_qwand_unify (Q : α -> hProp):
  XSimp (Hla, emp, emp) ((Q -∗ (Q ∗ Hla)) ∗ emp, emp, emp) := by
  srw ?XSimp ; hsimp
  sby srw qwand_equiv

lemma himpl_lr_htop :
  XSimp (emp, emp, emp) (emp, Hrg, emp) ->
  XSimp (Hla, emp, emp) (emp, (⊤ ∗ Hrg), emp) := by
  xsimp_lr_start=>?
  srw -(hstar_hempty_l Hla)
  apply himpl_hstar_trans_l=>// ; hstars_simp
  apply himpl_htop_r

lemma xsimpl_lr_hforall :
  (forall x, XSimp (emp, emp, Hla) (emp, emp, J x ∗ emp)) ->
  XSimp (Hla, emp, emp) ((hforall J) ∗ emp, emp, emp) := by
  xsimp_lr_start=>?
  apply himpl_hforall_r=> ?
  sdone

lemma xsimpl_lr_cancel_htop :
  XSimp (Hla, Hlw, Hlt) (Hra, (⊤ ∗ Hrg), Hrt) ->
  XSimp ((H ∗ Hla), Hlw, Hlt) (Hra, (⊤ ∗ Hrg), Hrt) := by
  xsimp_lr_start
  srw (hstar_comm_assoc Hra) -[2]hstar_htop_htop ; hsimp=>?
  apply himpl_frame_lr=>//
  apply himpl_htop_r

lemma xsimpl_lr_cancel_same_hsingle :
  XSimp (Hla, Hlw, Hlt) (Hra, Hrg, Hrt) →
  v1 = v2 →
  XSimp (p ~~> v1 ∗ Hla, Hlw, Hlt) (Hra, Hrg, p ~~> v2 ∗ Hrt) := by
  move=> ?? ; subst v1
  xsimp_lr_start
  hstars_simp
  sby srw (hstar_comm Hrt) (hstar_comm Hrg) ; hsimp

lemma xsimp_lr_exit :
  Hla ==> Hra ∗ Hrg ->
  XSimp (Hla, emp, emp) (Hra, Hrg, emp) := by
  sby srw ?XSimp ; hsimp

lemma qstar_simp (Q1 : α -> hProp) :
  (Q1 ∗ H) x = Q1 x ∗ H := by rfl


/- ----- Tactic for cancelling [hsingle] assertions ----- -/

def xsimp_pick_same_pointer (p hla : Term) : TacticM Unit := withMainContext do
  let p  <- Tactic.elabTerm p none
  hstar_search hla fun i h' last? => do
    match h' with
      | `(hsingle $p' $_) =>
        if p'.isMVarStx then throwError "not equal" else
        let p' <- Tactic.elabTerm p' none
        let .true <-
          withAssignableSyntheticOpaque <| isDefEq p' p | throwError "not equal"
      | _ => throwError "not equal"
    xsimp_pick i last?

lemma val_int_congr :
  n1 = n2 →
  val.val_int n1 = val.val_int n2 := by
  sdone

lemma val_loc_congr :
  n1 = n2 →
  val.val_loc n1 = val.val_loc n2 := by
  sdone


/- TODO: Extend this with some equality over values -/
elab "xsimp_hsingle_discharge" : tactic =>
  withAssignableSyntheticOpaque {|
    -- try congruence lemma
    (try apply val_int_congr
     try apply val_loc_congr
     try rfl
     try sdone) |}


/- ============ LHS xsimp step ============ -/

def xsimp_hwand_hstars_l (hla hs : Term) :=
  hstar_search hs fun i h last? => do
    -- let hstar_pick := hstar_pick_lemma i last?
    {| apply xsimp_l_hwand_reorder
       · apply $(hstar_pick_lemma i last?) |}
    match h with
    | `(hempty) => {| apply xsimpl_l_cancel_hwand_hstar_hempty |}
    | _ => xsimp_pick_same h hla; {| apply xsimp_l_cancel_hwand_hstar |}

def xsimp_apply_intro_names (lem : Name) (xs : Syntax) : TacticM Unit :=
  let lem := mkIdent lem
  match xs with
  | `(Lean.explicitBinders| $xs:unbracketedExplicitBinders) =>
    match xs with
    | `(unbracketedExplicitBinders| $[$xs]* : $_)
    | `(unbracketedExplicitBinders| $[$xs]*) =>
      for x in xs do
        match x with
        | `(binderIdent| $x:ident) =>
          {| apply $lem; intro $x:ident |}
        | `(binderIdent| $_:hole) =>
          {| apply $lem; unhygienic intro |}
        | _ => throwError "xsimp_l_exists: @ unreachable 2"
    | _ => throwError "xsimp_l_exists: @ unreachable 3"
  | `(Lean.explicitBinders| $[$xs]*) =>
      for x in xs do
        match x with
        | `(Lean.bracketedExplicitBinders| ($x:ident : $_) ) =>
          {| apply $lem; intro $x:ident |}
        | _ => throwError "xsimp_l_exists: @ unreachable 1"
  | _ => throwError "xsimp_l_exists: @ unreachable 3"
/- H₁ ∗ ... ∗ ==> H₁ -∗ ....  -/
macro "simpNums" : tactic =>
  `(tactic| (try simp only [foo, foo', foo''] at *
             try simp only [foo'''] at *
             try dsimp at *))

partial def xsimp_step_l (xsimp : XSimpR) (cancelWand := true) : TacticM Unit := do
  trace[xsimp] "LHS step"
  match xsimp.hlt, xsimp.hlw with
  | `(@HStar.hStar hProp hProp $_ $_ $h $_), _ =>
    match h with
    | `(hempty)         => {| apply xsimp_l_hempty |}
    | `(hpure $_)        =>
      let n <- fresh `n
      revExt.modifySSR (n :: ·)
      {| apply xsimp_l_hpure; intro $n:ident |}
    | `(@HStar.hStar hProp hProp $_ $_ $h1 $h2)   =>
      withAssignableSyntheticOpaque {| erw [@hstar_assoc $h1 $h2]; simpNums |}
      -- rewriteTarget (<- `(@hstar_assoc $h1 $h2)) false
      /- we know that here should be another LHS step -/
      xsimp_step_l (<- XSimpRIni) cancelWand
    | `(@hexists $_ fun ($x:ident : $_) => $_) =>
      revExt.modifySSR (x :: ·)
      {| apply xsimp_l_hexists; intro $x:term |}
    | `(@HWand.hWand hProp hProp $_ $_ $_ $_)    => {| apply xsimp_l_acc_wand |}
    | `(@HWand.hWand $_    $_    $_ $_ $_ $_)   => {| apply xsimp_l_acc_wand |}
    | _              => {| apply xsimp_l_acc_other |}
  | `(hempty), `(@HStar.hStar hProp hProp $_ $_ $h1 $_) =>
    match h1 with
    | `(@HWand.hWand hProp hProp $_ $_ $h1 $_) =>
      match h1 with
      | `(hempty) => {| apply xsimp_l_cancel_hwand_hempty |}
      | `(@HStar.hStar hProp hProp $_ $_ $_ $_) => xsimp_hwand_hstars_l xsimp.hla h1
      | _ => try
          let .true := cancelWand | failure
          xsimp_pick_same h1 xsimp.hla
          {| apply xsimp_l_cancel_hwand |}
        catch _ => {| apply xsimp_l_keep_wand |}
    | `(@HWand.hWand $_ $_ $_ $_ $q1 $_) =>
      try
        let .true := cancelWand | failure
        xsimp_pick_applied q1 xsimp.hla
        {| apply xsimp_l_cancel_qwand |}
      catch _ => {| apply xsimp_l_keep_wand |}
    | _ => throwError "xsimp_step_l: @ unreachable"
  | _, _ => throwError "xsimp_step_l: @ unreachable"

/- ============ RHS xsimp step ============ -/
declare_syntax_cat hint

syntax term : hint
syntax "?" : hint

declare_syntax_cat hints
syntax "[" (ppSpace colGt hint),* "]" : hints

def eApplyAndName (lem : Name) (mvarName : Name) : TacticM Unit := withMainContext do
    let gs <- getUnsolvedGoals
    let [g, ex] <- gs[0]!.applyConst lem | throwError "eApplyAndName: should be two goals"
    let nm <- fresh mvarName
    ex.setTag nm.getId
    ex.setUserName nm.getId
    setGoals $ g :: gs.tail


def xsimp_r_hexists_apply_hints (x : Ident) : TacticM Unit := do
  let hints <- hintExt.getSSR
  match hints with
  | [] =>
    trace[xsimp] "no hints"
    eApplyAndName `xsimp_r_hexists $ `xsimp ++ x.getId
  | h :: hs =>
    hintExt.setSSR hs
    match h with
    | `(hint| ?)       => eApplyAndName `xsimp_r_hexists $ `xsimp ++ x.getId
    | `(hint| $t:term) => {| apply (@xsimp_r_hexists _ $t) |}
    | _ => throwError "xsimp_r_hexists_apply_hints: @ unreachable"

partial def xsimp_step_r (xsimp : XSimpR) : TacticM Unit := do
  trace[xsimp] "RHS step"
  trace[xsimp] "hrt: {xsimp.hrt}"
  match xsimp.hlw, xsimp.hlt, xsimp.hrt with
  | `(hempty), `(hempty), `(@HStar.hStar hProp hProp $_ $_ $h $_) =>
    /- TODO: implement hook -/
    try
      trace[xsimp] "xsimp_r deals with: {h}"
      match h with
      | `(hempty) => {| apply xsimp_r_hempty |}
      | `(hpure $_) => {| apply xsimp_r_hpure |}
      | `(@HStar.hStar hProp hProp $_ $_ $h1 $h2) =>
        {| erw [@hstar_assoc $h1 $h2];
           simpNums |} -- HACK: Numbers are printed with explicict coercions in the goal.
                       -- Somehow rewite adds them as well. So we need to remove them
         /- we know that here should be another RHS step -/
        xsimp_step_r (<- XSimpRIni)
      | `(@HWand.hWand hProp hProp $_ $_ $h1 $_) =>
        match h1 with
        | `(hpure $_) => {| apply xsimp_r_keep |}
        | _ => {| apply xsimp_r_hwand_same |}
      | `(htop) =>
        match xsimp.hrg with
        | `(hempty) =>
          {| apply xsimpl_r_hgc_or_htop |}
          repeat'' do
            xsimp_pick_same h xsimp.hla
            {| apply xsimp_lr_cancel_same |}
        | `(@HStar.hStar hProp hProp $_ $_ htop hempty) => {| apply xsimpl_r_htop_drop |}
        | _ => throwError "xsimp_step_r: @ unreachable"
      | `(@hexists $_ fun ($x:ident : $_) => $_) => xsimp_r_hexists_apply_hints x
      | `(protect $_) => {| apply xsimp_r_keep |}
      | `(hsingle $x $_) =>
        -- dbg_trace "here: {x}"
        if x.isMVarStx then
          {| apply xsimp_r_keep |}
        else
          xsimp_pick_same_pointer x xsimp.hla
          -- let g <- getMainTarget
          -- trace[xsimp] g
          {| apply xsimpl_lr_cancel_same_hsingle <;>
             xsimp_hsingle_discharge |}
      | _ =>
        if h.isMVarStx then
          {| apply xsimp_r_keep |}
        else
        xsimp_pick_same h xsimp.hla
        {| apply xsimp_lr_cancel_same |}
    catch ex =>
      trace[xsimp] ex.toMessageData
      {| apply xsimp_r_keep |}
  | _, _, _ => throwError "not implemented"

/- ============ LHS/RHS xsimp step ============ -/

def xsimp_step_lr (xsimp : XSimpR) : TacticM Unit := do
  trace[xsimp] "LHS/RHS step"
  match xsimp.hrg with
  | `(hempty) =>
    match xsimp.hra with
    | `(@HStar.hStar hProp hProp $_ $_ $h1 hempty) =>
      if h1.isMVarStx then
        withAssignableSyntheticOpaque {| hsimp; apply himpl_lr_refl |}
        return ( )
      match h1 with
      | `(@HWand.hWand hProp hProp $_ $_ $h1 $_) =>
        match h1 with
        | `(hpure False) => {| apply xsimp_lr_hwand_hfalse |}
        | _ => /- TODO: flip -/ xsimp_flip_acc_lr xsimp.hla xsimp.hra ; {| apply xsimp_lr_hwand |}
      | `(@HWand.hWand $_   $_    $_ $_ $h1 $_) =>
        xsimp_flip_acc_lr xsimp.hla xsimp.hra ;
        try
          let .true := h1.isMVarStx | failure
          {| apply himpl_lr_qwand_unify |}
        catch _ =>
          {| first | apply xsimpl_lr_qwand_unit
                   | apply xsimpl_lr_qwand; unhygienic intro
             try simp only [qstar_simp] |}
      | `(@hforall $_ fun ($x : $_) => $_) => /- TODO: flip -/
        {| xsimp_flip_acc_l $xsimp.hla ; apply xsimpl_lr_hforall; intro $x:term |}
      | _ => /- TODO: flip -/ xsimp_flip_acc_lr xsimp.hla xsimp.hra ; {| apply xsimp_lr_exit |}
    | `(hempty) => {| first | apply himpl_lr_refl | apply xsimp_lr_exit |}
    | _ => /- TODO: flip -/ xsimp_flip_acc_lr xsimp.hla xsimp.hra ; {| apply xsimp_lr_exit |}
  | `(@HStar.hStar hProp hProp $_ $_ htop hempty) => {| first | apply himpl_lr_htop | apply xsimp_lr_exit |}
  | _ => /- TODO: flip -/ xsimp_flip_acc_lr xsimp.hla xsimp.hra ; {| apply xsimp_lr_exit |}


/- ============ Tactic Notations ============ -/

elab "xsimp_step" : tactic => do
  let xsimp <- XSimpRIni
  /- TODO: optimise.
    Sometimes we tell that some transitions are not availible at the moment.
    So it might be possible to come up with something better than trying all
    transitions one by one -/
  withMainContext do
    xsimp_step_l  xsimp <|>
    xsimp_step_r  xsimp <|>
    xsimp_step_lr xsimp

elab "xsimp_step_l_tac" : tactic => do
  let xsimp <- XSimpRIni
  withMainContext do
    xsimp_step_l  xsimp

elab "xsimp_step_r_tac" : tactic => do
  let xsimp <- XSimpRIni
  withMainContext do
    xsimp_step_r  xsimp

elab "xsimp_step_lr_tac" : tactic => do
  let xsimp <- XSimpRIni
  withMainContext do
    xsimp_step_lr  xsimp

elab "rev_pure" : tactic => do
  {| try subst_vars |}
  for n in <- revExt.getSSR do
    withMainContext do
    {| try  revert $n:ident |}
  revExt.setSSR []


elab "xsimp_handle_qimpl" : tactic => do
  match_expr <- getMainTarget with
  | qimpl tp _ q2 =>
    if q2.isMVar then
      {| apply qimpl_refl |}
    else if tp.isConstOf `Unit then
      {| scase |}
    else let r <- fresh `r; {| intros $r |}
  | himpl _ h2 =>
     if h2.isMVar then
      {| apply himpl_refl |}
     else return ( )
  | Eq tp _ _ =>
    let_expr hProp := tp | throwError "not a goal for xsimp/xpull"
    {| apply himpl_antisym |}
  | Eq tp _ _ =>
    let .some (_, tp) := tp.arrow? | throwError "not a goal for xsimp/xpull"
    let_expr hProp := tp | throwError "not a goal for xsimp/xpull"
    {| ext; apply himpl_antisym |}
  | _ => throwError "not a goal for xsimp/xpull"

macro "xpull_start" : tactic =>
  `(tactic|
     (xsimp_handle_qimpl
      apply xpull_protect
      apply xsimp_start_lemma))

macro "xsimp_start" : tactic =>
  `(tactic|
    (xsimp_handle_qimpl
     try apply xsimp_start_lemma))

macro "xpull" : tactic =>
  `(tactic| (
    xpull_start
    repeat' xsimp_step
    try rev_pure
    hsimp
  ))

elab "hide_mvars" : tactic => do
  let gs <- getUnsolvedGoals
  let mut gs' := []
  for g in gs do
    let tp <- Meta.inferType (<- g.getType)
    if tp.isProp then
      gs' := g :: gs'
  setGoals gs'.reverse


macro "xsimp" : tactic =>
  `(tactic| (
    xsimp_start
    repeat xsimp_step
    try rev_pure
    try hide_mvars
    try hsimp
    rotate_left

  ))

elab "xsimp" ls:hints : tactic => do
  match ls with
  | `(hints| [ $[$hs],* ]) =>
    hintExt.setSSR hs.toList
    {| xsimp_start
       repeat xsimp_step
       try rev_pure
       try hsimp
       rotate_left
        |}
  | _ => throwError "xsimp: unreachable"

/- **============ Test Cases ============** -/
section

lemma dup_lemma (p : Prop) : p -> p -> p := by sdone

partial def dup (n : Nat) : TacticM Unit := do
  match n with
  | 0 => {|skip|}
  | _ => dup (n-1); {| apply dup_lemma|}

elab "dup" n:num : tactic =>
  dup $ n.getNat -1

/- [hstar_pick] -/
section

local elab "pick" i:num : tactic =>
  let l := hstar_pick_lemma i.getNat false
  {|apply $l|}

local elab "pickl" i:num : tactic =>
  let l := hstar_pick_lemma i.getNat true
  {|apply $l|}

-- example :
--   (forall H, H1 ∗ H2 ∗ H3 ∗ H4 = H -> H = Hresult -> True) -> True := by
--   intro M
--   dup 2 <;> eapply M
--   { pick 3 }
--   { admit }
--   { pickl 4 }
--   { admit }

/- `xsimp_pick` -/

local elab "xsimp_pick" i:num : tactic =>
  xsimp_pick i.getNat false

local elab "xsimp_pickl" i:num : tactic =>
  xsimp_pick i.getNat true

local elab "xsimp_pick_same" h:term : tactic => do
  let xsimp <- XSimpRIni
  xsimp_pick_same h xsimp.hla

local elab "xsimp_pick_applied" h:term : tactic => do
  let xsimp <- XSimpRIni
  xsimp_pick_applied h xsimp.hla


-- example (Q : Bool -> _):
--   (forall HX HY,
--     XSimp ((H1 ∗ H2 ∗ H3 ∗ Q true ∗ (⌜P⌝ -∗ HX) ∗ HY ∗ emp), Hlw, Hlt)
--            (Hra, Hrg, Hrt)
--   -> True) -> True := by
--   move=> M
--   eapply M
--   xsimp_pick 2
--   xsimp_pick_same H3
--   xsimp_pick_applied Q
--   xsimp_pick_same H2
--   xsimp_pick_same H3
--   xsimp_pick_same ⌜True⌝
--   xsimp_pick_same (⌜P⌝ -∗ H1)
--   admit

/- `xsimp/xpull` -/

local macro "xpull0" : tactic => `(tactic| xpull_start)
local macro "xsimp0" : tactic => `(tactic| xsimp_start)
local macro "xsimp1" : tactic => `(tactic| xsimp_step)
local elab "xsimpl" : tactic => do
  xsimp_step_l (<- XSimpRIni) true
local elab "xsimpr" : tactic => do
  xsimp_step_r (<- XSimpRIni)

-- example :
--   (H1 ∗ emp ∗ (H2 ∗ (∃ʰ (y:Int) (z : Int) (n:Int), ⌜y = y + z + n⌝)) ∗ H3) ==> H :=
--   by
--     dup 2
--     { xpull0; xsimp1; xsimp1; xsimp1; xsimp1; xsimp1; xsimp1; xsimp1;
--       admit }
--     { xpull; admit }

-- example :
--   H1 ∗ H2 ∗ H3 ∗ H4 ==> H4 ∗ H3 ∗ H5 ∗ H2 :=
--   by
--     dup 3
--     { xpull; admit }
--     { xsimp0
--       xsimp1
--       xsimp1
--       xsimp1
--       xsimp1
--       xsimp1
--       xsimp1
--       xsimp1
--       xsimp1; xsimp1; admit }
--     xsimp; admit

-- /--
-- warning: declaration uses
-- ---
-- info: case xsimp_goal.a.a.a
-- H1 H2 H3 H4 H5 H6 H7 : hProp
-- ⊢ H1 ∗ H2 ∗ H4 ==> H5 ∗ H6 ∗ H7
-- -/
-- #guard_msgs in
-- example :
--   H1 ∗ H2 ∗ H3 ∗ H4 ==> H5 ∗ H3 ∗ H6 ∗ H7 := by
--   xsimp
--   trace_state
--   admit

example :
  H1 ∗ H2 ∗ H3 ∗ H4 ∗ H5 ==> H3 ∗ H1 ∗ H2 ∗ ⊤ := by
  xsimp

example (Q : Int -> _) :
  Q 4 ==> Q 3 ->
  H1 ∗ Q 4 ==> ∃ʰ x, Q x ∗ H1 :=
  by intro; xsimp[3]=> // /- TODO: handle hints -/

example :
  (forall H, H1 ∗ H2 ==> H -> True) -> True :=
  by sapply; xsimp

example :
  (forall H, H1 ==> H1 ∗ H -> True) -> True :=
  by sapply; xsimp

example :
  H1 ∗ H2 ∗ ⊤ ==> H1 ∗ ⊤ :=
  by xsimp

example :
  H1 ∗ H2 ∗ ⊤ ==> H1 ∗ ⊤ ∗ ⊤ :=
  by xsimp

example :
  (H1 -∗ (H2 -∗ H3)) ∗ H1 ∗ H4 ==> (H2 -∗ (H3 ∗ H4)) :=
  by
    dup 2
    { xsimp0;
      xsimp1; xsimp1; xsimp1; xsimp1; xsimp1; xsimp1;
      xsimp1; xsimp1; xsimp1; xsimp1; xsimp1; xsimp1;
      xsimp1; xsimp1; xsimp1; xsimp1; xsimp1; xsimp1;
      xsimp1; xsimp1  }
    { xsimp }

example (Q1 Q2 : α -> hProp) :
  H1 ∗ (H1 -∗ (Q1 -∗ Q2)) ∗ (Q1 x) ==> (Q2 x) := by
  xsimp

example :
  H1 ∗ H2 ==> H1 ∗ (H3 -∗ (H2 ∗ H3)) := by
  xsimp

example (Q1 Q2 : α -> hProp) :
   H1 ∗ (H1 -∗ (Q1 -∗ Q2)) ∗ (Q1 x) ==> (Q2 x) := by
  xsimp

example :
  H1 ∗ H2 ==> H1 ∗ (H3 -∗ (H2 ∗ H3)) := by
  xsimp

example :
  H1 ∗ H2 ==> H1 ∗ (Q1 -∗ (Q1 ∗ H2)) := by
  xsimp

example :
  H1 -∗ H4 ==> H5 ->
  (H2 ∗ ((H1 ∗ H2 ∗ H3) -∗ H4)) ∗ H3 ==> H5 := by
  move=> ?
  sby xsimp

example :
  (H1 ∗ H2 ∗ ((H1 ∗ H3) -∗ (H4 -∗ H5))) ∗ (H2 -∗ H3) ∗ H4 ==> H5 :=
  by xsimp

-- example :
--   (emp -∗ H1) ∗ H2 ==> H3 :=
--   by xsimp; admit

-- example :
--   ((H0 ∗ emp) -∗ emp -∗ H1) ∗ H2 ==> H3 := by
--   xsimp; admit

-- example (v2 : Int) :
--   H0 ∗ H1 ∗ p1 ~~> v1 ∗ p2 ~~> val.val_int (v2 * 1) ==> H2 ∗ p2 ~~> v2 ∗ H3 := by
--   xsimp
--   any_goals admit

-- example:
--   v = v' →
--   H1 ∗ p ~~> v ==> H1 ∗ p ~~> v' := by
--   move=> ?
--   xsimp

-- example:
--   H1 ∗ p1 ~~> v1 ∗ H2 ∗ p2 ~~> v2 ∗ H3 ==> H1 ∗ H2 ∗  p1 ~~> v1' ∗ p2 ~~> v2' := by
--   xsimp
--   all_goals admit

-- example :
--   H1 ∗ 2 ~~> v ==> (1 + 1) ~~> v ∗ H1 := by
--   xsimp

-- example :
--   x ~~> 1 ==> y ~~> 2 ∗ x ~~> 1 := by
--   xsimp; admit



-- set_option trace.xsimp true

-- example :
--   H1 ∗ H2 ∗ ((H1 ∗ H3) -∗ (H4 -∗ H5)) ∗ H4 ==> ((H2 -∗ H3) -∗ H5) := by
--   xsimp

-- local elab "put_hints" ls:hints : tactic => do
--   match ls with
--   | `(hints| [ $[$hs],* ]) =>
--     hintExt.setSSR hs.toList
--   | _ => throwError "xsimp: unreachable"

-- example (Q : Int -> Bool -> _) :
--   Q 4 true ==> Q 3 false ->
--   H1 ∗ Q 4 true ==> ∃ʰ x b, Q x b ∗ H1 := by
--   move=> ?
--   xsimp

-- example :
--   emp ==> (∃ʰ x, x ~~> 1) ∗ (∃ʰ x, x ~~> 2) := by
--   xsimp_start
--   xsimp_step
--   xsimp_step
--   xsimp_step
--   xsimp_step
end
end
