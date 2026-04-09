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

theorem arstepstar_add_complete_aux (e₁ e₂ : ArExpr V) (n₁ n₂ : Int) : ArStepStar V val e₁ (ArExpr.Const n₁) -> ArStepStar V val e₂ (ArExpr.Const n₂) -> ArStepStar V val (ArExpr.Add e₁ e₂) (ArExpr.Const (n₁ + n₂)) := by
  intro h₁ h₂
  apply chasles_step_star
  · exact arstepstar_add_left _ _ _ h₁
  · apply chasles_step_star
    · exact arstepstar_add_right n₁ _ _ h₂
    · apply StepStar.trans
      · exact ArStep.addConstConst n₁ n₂
      · apply StepStar.refl

theorem arstepstar_if_complete_aux (cond : BoolExpr V) (a b : ArExpr V) (bc : Bool) (na nb : Int) : BoolStepStar V val cond (BoolExpr.Const bc) -> ArStepStar V val a (ArExpr.Const na) -> ArStepStar V val b (ArExpr.Const nb) -> ArStepStar V val (ArExpr.If cond a b) (ArExpr.Const (if bc then na else nb)) := by
  intro hcond ha hb
  have hif : ArStepStar V val (ArExpr.If cond a b) (ArExpr.If (BoolExpr.Const bc) a b) :=
    ArStepStar.ifStep cond (BoolExpr.Const bc) a b hcond
  cases bc
  · have hfalse : ArStepStar V val (ArExpr.If (BoolExpr.Const false) a b) b :=
      step_to_stepstar V (ExprKind := ArExpr V) (Step := ArStep V) (val := val) (ArStep.ifCondFalse a b)
    exact chasles_step_star V (ExprKind := ArExpr V) (Step := ArStep V) (val := val) hif
      (chasles_step_star V (ExprKind := ArExpr V) (Step := ArStep V) (val := val) hfalse hb)
  · have htrue : ArStepStar V val (ArExpr.If (BoolExpr.Const true) a b) a :=
      step_to_stepstar V (ExprKind := ArExpr V) (Step := ArStep V) (val := val) (ArStep.ifCondTrue a b)
    exact chasles_step_star V (ExprKind := ArExpr V) (Step := ArStep V) (val := val) hif
      (chasles_step_star V (ExprKind := ArExpr V) (Step := ArStep V) (val := val) htrue ha)

theorem arstepstar_mul_complete_aux (e₁ e₂ : ArExpr V) (n₁ n₂ : Int) : ArStepStar V val e₁ (ArExpr.Const n₁) -> ArStepStar V val e₂ (ArExpr.Const n₂) -> ArStepStar V val (ArExpr.Mul e₁ e₂) (ArExpr.Const (n₁ * n₂)) := by
  intro h₁ h₂
  have h₁' := arstepstar_mul_left (V := V) (val := val) (e₁ := e₁) (e₁' := ArExpr.Const n₁) (e₂ := e₂) h₁
  have h₂' := arstepstar_mul_right (V := V) (val := val) (n := n₁) (e₂ := e₂) (e₂' := ArExpr.Const n₂) h₂
  have h₃ := step_to_stepstar (V := V) (Step := ArStep V) (val := val) (e := ArExpr.Mul (ArExpr.Const n₁) (ArExpr.Const n₂)) (e' := ArExpr.Const (n₁ * n₂)) (ArStep.mulConstConst n₁ n₂)
  exact chasles_step_star (V := V) (Step := ArStep V) h₁' (chasles_step_star (V := V) (Step := ArStep V) h₂' h₃)

theorem arstepstar_sub_complete_aux (e₁ e₂ : ArExpr V) (n₁ n₂ : Int) : ArStepStar V val e₁ (ArExpr.Const n₁) -> ArStepStar V val e₂ (ArExpr.Const n₂) -> ArStepStar V val (ArExpr.Sub e₁ e₂) (ArExpr.Const (n₁ - n₂)) := by
  intro h₁ h₂
  have h₁' : ArStepStar V val (ArExpr.Sub e₁ e₂) (ArExpr.Sub (ArExpr.Const n₁) e₂) := by
    exact arstepstar_sub_left (V := V) e₁ (ArExpr.Const n₁) e₂ h₁
  have h₂' : ArStepStar V val (ArExpr.Sub (ArExpr.Const n₁) e₂) (ArExpr.Sub (ArExpr.Const n₁) (ArExpr.Const n₂)) := by
    exact arstepstar_sub_right (V := V) n₁ e₂ (ArExpr.Const n₂) h₂
  have h₃ : ArStepStar V val (ArExpr.Sub (ArExpr.Const n₁) (ArExpr.Const n₂)) (ArExpr.Const (n₁ - n₂)) := by
    exact step_to_stepstar (Step := ArStep V) (V := V) (val := val) (e := ArExpr.Sub (ArExpr.Const n₁) (ArExpr.Const n₂)) (e' := ArExpr.Const (n₁ - n₂)) (ArStep.subConstConst n₁ n₂)
  exact chasles_step_star (V := V) (Step := ArStep V) (val := val) h₁' (chasles_step_star (V := V) (Step := ArStep V) (val := val) h₂' h₃)

mutual

theorem eval_completeness (e: ArExpr V) : ArStepStar V val e (ArExpr.Const (eval V val e)) := by
  let rec go (e : ArExpr V) : ArStepStar V val e (ArExpr.Const (eval V val e)) :=
    match e with
    | ArExpr.Const n => by
        simpa [eval] using (ArStepStar.refl (V := V) val (ArExpr.Const n))
    | ArExpr.Var v => by
        simpa [eval] using
          (step_to_stepstar (V := V) (Step := ArStep V) (val := val)
            (e := ArExpr.Var v) (e' := ArExpr.Const (val v))
            (ArStep.getVarValue (val := val) v))
    | ArExpr.Add e₁ e₂ => by
        simpa [eval] using
          (arstepstar_add_complete_aux (V := V) (val := val)
            e₁ e₂ (eval V val e₁) (eval V val e₂) (go e₁) (go e₂))
    | ArExpr.Sub e₁ e₂ => by
        simpa [eval] using
          (arstepstar_sub_complete_aux (V := V) (val := val)
            e₁ e₂ (eval V val e₁) (eval V val e₂) (go e₁) (go e₂))
    | ArExpr.Mul e₁ e₂ => by
        simpa [eval] using
          (arstepstar_mul_complete_aux (V := V) (val := val)
            e₁ e₂ (eval V val e₁) (eval V val e₂) (go e₁) (go e₂))
    | ArExpr.If cond a b => by
        have hcond := eval_bool_completeness (val := val) cond
        simpa [eval] using
          (arstepstar_if_complete_aux (V := V) (val := val)
            cond a b (eval_bool V val cond) (eval V val a) (eval V val b)
            hcond (go a) (go b))
  exact go e

theorem eval_bool_completeness (e: BoolExpr V): BoolStepStar V val e (BoolExpr.Const (eval_bool V val e)) := by
  sorry

end
