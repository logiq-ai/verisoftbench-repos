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

theorem eval_bool_completeness (e: BoolExpr V): BoolStepStar V val e (BoolExpr.Const (eval_bool V val e)) := by sorry
