import ExprEval.Steps
import ExprEval.Lemmas

variable (V: Type)

theorem eval_soundness (e: ArExpr V) (v: Int) :
    ArStepStar V val e (ArExpr.Const v) -> eval V val e = v := by
    intro h
    exact arstepstar_preserves_eval _ _ h

theorem eval_bool_soundness (e: BoolExpr V) (b: Bool) :
    BoolStepStar V val e (BoolExpr.Const b) -> eval_bool V val e = b := by
    intro h
    exact boolstepstar_preserves_eval_bool _ _ h

theorem eval_completeness (e: ArExpr V) : ArStepStar V val e (ArExpr.Const (eval V val e)) := by sorry

theorem eval_bool_completeness (e: BoolExpr V): BoolStepStar V val e (BoolExpr.Const (eval_bool V val e)) := by
  refine @BoolExpr.rec V (fun _ => True) (fun e => BoolStepStar V val e (BoolExpr.Const (eval_bool V val e))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro a
    trivial
  · intro a a₁ _ _
    trivial
  · intro a a₁ _ _
    trivial
  · intro a a₁ _ _
    trivial
  · intro a
    trivial
  · intro a a₁ a₂ _ _ _
    trivial
  · intro b
    apply BoolStepStar.refl
  · intro l r _ _
    have hl : ArStepStar V val l (ArExpr.Const (eval V val l)) := eval_completeness (V := V) (val := val) l
    have hr : ArStepStar V val r (ArExpr.Const (eval V val r)) := eval_completeness (V := V) (val := val) r
    have hleft : BoolStepStar V val (BoolExpr.Less l r) (BoolExpr.Less (ArExpr.Const (eval V val l)) r) :=
      BoolStepStar.lessArStepStarLeft (V := V) (val := val) l (ArExpr.Const (eval V val l)) r hl
    have hright : BoolStepStar V val (BoolExpr.Less (ArExpr.Const (eval V val l)) r) (BoolExpr.Less (ArExpr.Const (eval V val l)) (ArExpr.Const (eval V val r))) :=
      BoolStepStar.lessArStepStarRight (V := V) (val := val) (ArExpr.Const (eval V val l)) r (ArExpr.Const (eval V val r)) hr
    have hconst : BoolStepStar V val (BoolExpr.Less l r) (BoolExpr.Less (ArExpr.Const (eval V val l)) (ArExpr.Const (eval V val r))) :=
      chasles_step_star (V := V) (Step := BoolStep V) (val := val) hleft hright
    by_cases hlt : eval V val l < eval V val r
    · have htail : BoolStepStar V val (BoolExpr.Less (ArExpr.Const (eval V val l)) (ArExpr.Const (eval V val r))) (BoolExpr.Const true) :=
        step_to_stepstar (V := V) (Step := BoolStep V) (val := val) (e := BoolExpr.Less (ArExpr.Const (eval V val l)) (ArExpr.Const (eval V val r))) (e' := BoolExpr.Const true) (BoolStep.lessConstConstTrue _ _ hlt)
      simpa [eval_bool, hlt] using chasles_step_star (V := V) (Step := BoolStep V) (val := val) hconst htail
    · have hge : eval V val l >= eval V val r := Int.not_lt.mp hlt
      have htail : BoolStepStar V val (BoolExpr.Less (ArExpr.Const (eval V val l)) (ArExpr.Const (eval V val r))) (BoolExpr.Const false) :=
        step_to_stepstar (V := V) (Step := BoolStep V) (val := val) (e := BoolExpr.Less (ArExpr.Const (eval V val l)) (ArExpr.Const (eval V val r))) (e' := BoolExpr.Const false) (BoolStep.lessConstConstFalse _ _ hge)
      simpa [eval_bool, hlt] using chasles_step_star (V := V) (Step := BoolStep V) (val := val) hconst htail
  · intro l r _ _
    have hl : ArStepStar V val l (ArExpr.Const (eval V val l)) := eval_completeness (V := V) (val := val) l
    have hr : ArStepStar V val r (ArExpr.Const (eval V val r)) := eval_completeness (V := V) (val := val) r
    have hleft : BoolStepStar V val (BoolExpr.Eq l r) (BoolExpr.Eq (ArExpr.Const (eval V val l)) r) :=
      BoolStepStar.eqArStepStarLeft (V := V) (val := val) l (ArExpr.Const (eval V val l)) r hl
    have hright : BoolStepStar V val (BoolExpr.Eq (ArExpr.Const (eval V val l)) r) (BoolExpr.Eq (ArExpr.Const (eval V val l)) (ArExpr.Const (eval V val r))) :=
      BoolStepStar.eqArStepStarRight (V := V) (val := val) (ArExpr.Const (eval V val l)) r (ArExpr.Const (eval V val r)) hr
    have hconst : BoolStepStar V val (BoolExpr.Eq l r) (BoolExpr.Eq (ArExpr.Const (eval V val l)) (ArExpr.Const (eval V val r))) :=
      chasles_step_star (V := V) (Step := BoolStep V) (val := val) hleft hright
    by_cases heq : eval V val l = eval V val r
    · have htail : BoolStepStar V val (BoolExpr.Eq (ArExpr.Const (eval V val l)) (ArExpr.Const (eval V val r))) (BoolExpr.Const true) :=
        step_to_stepstar (V := V) (Step := BoolStep V) (val := val) (e := BoolExpr.Eq (ArExpr.Const (eval V val l)) (ArExpr.Const (eval V val r))) (e' := BoolExpr.Const true) (BoolStep.eqConstConstTrue _ _ heq)
      simpa [eval_bool, heq, beq_iff_eq] using chasles_step_star (V := V) (Step := BoolStep V) (val := val) hconst htail
    · have hne : eval V val l != eval V val r := by
        simpa [bne_iff_ne] using heq
      have htail : BoolStepStar V val (BoolExpr.Eq (ArExpr.Const (eval V val l)) (ArExpr.Const (eval V val r))) (BoolExpr.Const false) :=
        step_to_stepstar (V := V) (Step := BoolStep V) (val := val) (e := BoolExpr.Eq (ArExpr.Const (eval V val l)) (ArExpr.Const (eval V val r))) (e' := BoolExpr.Const false) (BoolStep.eqConstConstFalse _ _ hne)
      have hbeq : (eval V val l == eval V val r) = false := by
        simp [beq_iff_eq, heq]
      simpa [eval_bool, hbeq] using chasles_step_star (V := V) (Step := BoolStep V) (val := val) hconst htail
  · intro e ih
    have hstep : BoolStepStar V val (BoolExpr.Not e) (BoolExpr.Not (BoolExpr.Const (eval_bool V val e))) :=
      BoolStepStar.notStep (V := V) (val := val) e (BoolExpr.Const (eval_bool V val e)) ih
    have htail : BoolStepStar V val (BoolExpr.Not (BoolExpr.Const (eval_bool V val e))) (BoolExpr.Const (!(eval_bool V val e))) :=
      step_to_stepstar (V := V) (Step := BoolStep V) (val := val) (e := BoolExpr.Not (BoolExpr.Const (eval_bool V val e))) (e' := BoolExpr.Const (!(eval_bool V val e))) (BoolStep.notIsBoolNot _)
    simpa [eval_bool] using chasles_step_star (V := V) (Step := BoolStep V) (val := val) hstep htail
  · intro l r ihl ihr
    have hleft : BoolStepStar V val (BoolExpr.And l r) (BoolExpr.And (BoolExpr.Const (eval_bool V val l)) r) :=
      BoolStepStar.andStepLeft (V := V) (val := val) l (BoolExpr.Const (eval_bool V val l)) r ihl
    cases hbl : eval_bool V val l with
    | false =>
        have hleft' : BoolStepStar V val (BoolExpr.And l r) (BoolExpr.And (BoolExpr.Const false) r) := by
          simpa [hbl] using hleft
        have hstep : BoolStepStar V val (BoolExpr.And (BoolExpr.Const false) r) (BoolExpr.Const false) :=
          step_to_stepstar (V := V) (Step := BoolStep V) (val := val) (e := BoolExpr.And (BoolExpr.Const false) r) (e' := BoolExpr.Const false) (BoolStep.andLeftShortCircuit r)
        simpa [eval_bool, hbl] using chasles_step_star (V := V) (Step := BoolStep V) (val := val) hleft' hstep
    | true =>
        have hleft' : BoolStepStar V val (BoolExpr.And l r) (BoolExpr.And (BoolExpr.Const true) r) := by
          simpa [hbl] using hleft
        have hstep : BoolStepStar V val (BoolExpr.And (BoolExpr.Const true) r) r :=
          step_to_stepstar (V := V) (Step := BoolStep V) (val := val) (e := BoolExpr.And (BoolExpr.Const true) r) (e' := r) (BoolStep.andLeftTrue r)
        have hmid : BoolStepStar V val (BoolExpr.And l r) r :=
          chasles_step_star (V := V) (Step := BoolStep V) (val := val) hleft' hstep
        simpa [eval_bool, hbl] using chasles_step_star (V := V) (Step := BoolStep V) (val := val) hmid ihr
  · intro l r ihl ihr
    have hleft : BoolStepStar V val (BoolExpr.Or l r) (BoolExpr.Or (BoolExpr.Const (eval_bool V val l)) r) :=
      BoolStepStar.orStepLeft (V := V) (val := val) l (BoolExpr.Const (eval_bool V val l)) r ihl
    cases hbl : eval_bool V val l with
    | false =>
        have hleft' : BoolStepStar V val (BoolExpr.Or l r) (BoolExpr.Or (BoolExpr.Const false) r) := by
          simpa [hbl] using hleft
        have hstep : BoolStepStar V val (BoolExpr.Or (BoolExpr.Const false) r) r :=
          step_to_stepstar (V := V) (Step := BoolStep V) (val := val) (e := BoolExpr.Or (BoolExpr.Const false) r) (e' := r) (BoolStep.orLeftFalse r)
        have hmid : BoolStepStar V val (BoolExpr.Or l r) r :=
          chasles_step_star (V := V) (Step := BoolStep V) (val := val) hleft' hstep
        simpa [eval_bool, hbl] using chasles_step_star (V := V) (Step := BoolStep V) (val := val) hmid ihr
    | true =>
        have hleft' : BoolStepStar V val (BoolExpr.Or l r) (BoolExpr.Or (BoolExpr.Const true) r) := by
          simpa [hbl] using hleft
        have hstep : BoolStepStar V val (BoolExpr.Or (BoolExpr.Const true) r) (BoolExpr.Const true) :=
          step_to_stepstar (V := V) (Step := BoolStep V) (val := val) (e := BoolExpr.Or (BoolExpr.Const true) r) (e' := BoolExpr.Const true) (BoolStep.orLeftShortCircuit r)
        simpa [eval_bool, hbl] using chasles_step_star (V := V) (Step := BoolStep V) (val := val) hleft' hstep

