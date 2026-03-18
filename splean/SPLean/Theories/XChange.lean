import Lean.Elab.Tactic

import SPLean.Theories.HProp
import SPLean.Common.Util
import SPLean.Theories.XSimp

open Lean Lean.Expr Lean.Meta Qq
open Lean Elab Command Term Meta Tactic

/- ----------------------------------------------------------------- -/
/-* *** Tactic [xchange] -/

/-* [xchange] performs rewriting on the LHS of an entailment.
  Essentially, it applies to a goal of the form [H1 ∗ H2 ==> H3],
  and exploits an entailment [H1 ==> H1'] to replace the goal with
  [H1' \* H2 ==> H3].

  The tactic is actually a bit more flexible in two respects:
  - it does not force the LHS to be exactly of the form [H1 \* H2]
  - it takes as argument any lemma, whose instantiation result in
    a heap entailment of the form [H1 ==> H1'].

  Concretely, the tactic is just a wrapper around an application
  of the lemma called [xchange_lemma], which appears below.

  [xchanges] combines a call to [xchange] with calls to [xsimpl]
  on the subgoals. -/

lemma xchange_lemma :
  H1 ==> H2 ->
  H3 ==> H1 ∗ (H2 -∗ protect H4) ->
  H3 ==> H4 := by
  move=> M1 M2
  apply himpl_trans ; apply M2
  apply himpl_hstar_trans_l ; apply M1
  apply hwand_cancel

def toHimp (e : Expr) : MetaM Expr := do
  let eTy <- inferType e
  trace[xchange] "type of give hypothesis {eTy}"
  forallTelescope eTy fun xs eTy => do
    let himpl <- match_expr eTy with
      | himpl _ _ => return e
      | qimpl _ _ _ => return e
      | Eq _ _ _  =>
        mkAppOptM `himpl_of_eq #[.none, .none, eTy]
      | _        => throwError "Expected a heap entailment or an equality"
    mkForallFVars xs himpl

def xchangeApply (l : Expr) : MVarId -> MetaM (List MVarId) := fun goal => do
  let g :: gs <- goal.applyConst `xchange_lemma | throwError "Expected a heap entailment"
  let gs' <- g.apply $ <- toHimp l
  return gs ++ gs'

def xcahngeCore (l : Expr) : MVarId -> MetaM (List MVarId) := fun goal => do
  let goal <-
    match_expr <- goal.getType with
    | himpl _ _ => pure goal
    | qimpl _ _ _ => pure (<- goal.intro1P).2
    | _ => throwError "Expected a heap entailment"
  xchangeApply l goal

elab "xchange_core" l:term : tactic => withMainContext do
  let (l, mvs) <- Tactic.elabTermWithHoles l none `xchange (allowNaturalHoles := true)
  let gs <- xcahngeCore l (<- getMainGoal)
  replaceMainGoal $ gs ++ mvs

macro "xchange" l:term : tactic =>
  `(tactic| (xchange_core $l; xsimp))

macro "xchanges" l:term : tactic =>
  `(tactic| (xchange_core $l; unfold protect; xsimp))

/- ----------------------------------------------------------------- -/
/-* *** [xchange] demos -/

-- set_option trace.xchange true

-- example :
--   H1 ==> H2 ∗ H3 ->
--   H1 ∗ H4 ==> (H5 -∗ H6) := by
--   intro M
--   dup 2
--   { xchange M; admit }
--   xchanges M; admit

example (Q : α -> hProp) :
  H1 ==> (∃ʰ x, Q x ∗ (H2 -∗ H3)) ->
  H1 ∗ H2 ==> ∃ʰ x, Q x ∗ H3 := by
  intro M
  dup 2
  { xchange M=> x; xsimp }
  xchanges M

-- set_option pp.explicit true
-- set_option pp.notation false

example (Q : Int -> hProp) :
  (∀ {α :Type} (x:α) (J:α->hProp), (hforall J) ==> (J x)) ->
  (h∀ x, Q x) ∗ H ==> Q 2 ∗ ⊤ := by
  intro M
  xchange M (2 : Int)
  xsimp

-- def xcahngeCore (l : Expr) : TacticM Unit := do
--   let goal <- getMainGoal
--   let goalTy <- getMainTarget
--   let _ <- match_expr goalTy with
--   | himpl _ _ => return ( )
--   | qimpl _ _ _ => goal.intro1P
--   | _ => throwError "Expected a heap entailment"
--     xchangeApply
