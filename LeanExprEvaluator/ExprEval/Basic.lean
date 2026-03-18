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

mutual
    theorem eval_completeness (e: ArExpr V) : ArStepStar V val e (ArExpr.Const (eval V val e)) := by
        cases e with
        | Const x =>
            simp [eval]
            exact ArStepStar.refl _ _
        | Add e₁ e₂ =>
            have ih1 := eval_completeness e₁ (val := val)
            have ih2 := eval_completeness e₂ (val := val)
            simp [eval]
            have a := arstepstar_add_left _ _ e₂ ih1
            have b := arstepstar_add_right (eval V val e₁) e₂ _ ih2
            have c := ArStep.addConstConst (val := val) (eval V val e₁) (eval V val e₂)
            have d := ArStepStar.trans _ _ _ c (ArStepStar.refl _ (ArExpr.Const (eval V val e₁ + eval V val e₂)))
            have e := chasles_step_star _ a (chasles_step_star _ b d)
            exact e
        | Sub e₁ e₂ =>
            have ih1 := eval_completeness e₁ (val := val)
            have ih2 := eval_completeness e₂ (val := val)
            simp [eval]
            have a := arstepstar_sub_left _ _ e₂ ih1
            have b := arstepstar_sub_right (eval V val e₁) e₂ _ ih2
            have c := ArStep.subConstConst (val := val) (eval V val e₁) (eval V val e₂)
            have d := ArStepStar.trans _ _ _ c (ArStepStar.refl _ (ArExpr.Const  (eval V val e₁ - eval V val e₂)))
            have e := chasles_step_star _ a (chasles_step_star _ b d)
            exact e
        | Mul e₁ e₂ =>
            have ih1 := eval_completeness e₁ (val := val)
            have ih2 := eval_completeness e₂ (val := val)
            simp [eval]
            have a := arstepstar_mul_left _ _ e₂ ih1
            have b := arstepstar_mul_right (eval V val e₁) e₂ _ ih2
            have c := ArStep.mulConstConst (val := val) (eval V val e₁) (eval V val e₂)
            have d := ArStepStar.trans _ _ _ c (ArStepStar.refl _ (ArExpr.Const (eval  V val e₁ * eval V val e₂)))
            have e := chasles_step_star _ a (chasles_step_star _ b d)
            exact e
        | Var var =>
            simp [eval]
            have a := ArStep.getVarValue var (val := val)
            have b := ArStepStar.refl val (ArExpr.Const (val var))
            exact ArStepStar.trans (val := val) _ _ _ a b
        | If cond a b =>
            simp [eval]
            cases h: (eval_bool V val cond)
            .   simp
                have h1 := ArStep.ifCondFalse a b (val := val)
                have h2 := eval_completeness b (val := val)
                have h3 := StepStar.trans _ _ _ h1 h2
                have h4 := eval_bool_completeness cond (val := val)
                rw [h] at h4
                have h5 := ArStepStar.ifStep _ _ a b h4
                exact chasles_step_star V h5 h3
            .   simp
                have h1 := ArStep.ifCondTrue a b (val := val)
                have h2 := eval_completeness a (val := val)
                have h3 := StepStar.trans _ _ _ h1 h2
                have h4 := eval_bool_completeness cond (val := val)
                rw [h] at h4
                have h5 := ArStepStar.ifStep _ _ a b h4
                exact chasles_step_star V h5 h3


    theorem eval_bool_completeness (e: BoolExpr V): BoolStepStar V val e (BoolExpr.Const (eval_bool V val e)) := by
        cases e with
        | Const b =>
            simp [eval_bool]
            apply BoolStepStar.refl
        | Not e =>
            simp [eval_bool]
            have ihn := eval_bool_completeness e (val := val)
            have h := BoolStepStar.notStep e _ ihn
            have h1 := BoolStep.notIsBoolNot (eval_bool V val e) (val := val)
            have h2 := (step_to_stepstar V h1)
            apply chasles_step_star V h h2
        | And l r =>
            have l_step := eval_bool_completeness l (val := val)
            have r_step := eval_bool_completeness r (val := val)
            simp [eval_bool]
            by_cases h: (eval_bool V val l)
            .   simp [and]
                rw [h]
                simp
                rw [h] at l_step
                have h1 := BoolStep.andLeftTrue r (val := val)
                have h2 := StepStar.trans _ _ _ h1 r_step
                have h3 := BoolStepStar.andStepLeft _ _ r l_step
                exact chasles_step_star V h3 h2

            .   replace h := eq_false_of_ne_true h
                rw [h]
                rw [h] at l_step
                simp [and]
                have h1 := BoolStepStar.andStepLeft _ _ r l_step
                have h2 := BoolStep.andLeftShortCircuit r (val := val)
                have h3 := step_to_stepstar V h2
                exact chasles_step_star V h1 h3
        | Or l r =>
            have l_step := eval_bool_completeness l (val := val)
            have r_step := eval_bool_completeness r (val := val)
            simp [eval_bool]
            by_cases h: (eval_bool V val l)
            .   rw [h]
                rw [h] at l_step
                simp [or]
                have h1 := BoolStepStar.orStepLeft _ _ r l_step
                have h2 := BoolStep.orLeftShortCircuit r (val := val)
                have h3 := step_to_stepstar V h2
                exact chasles_step_star V h1 h3

            .   replace h := eq_false_of_ne_true h
                rw [h]
                rw [h] at l_step
                simp
                have h1 := BoolStep.orLeftFalse r (val := val)
                have h2 := StepStar.trans _ _ _ h1 r_step
                have h3 := BoolStepStar.orStepLeft _ _ r l_step
                exact chasles_step_star V h3 h2
        | Eq l r =>
            simp [eval_bool]

            by_cases h: (eval V val l == eval V val r)

            .   replace h := eq_of_beq h
                rw [h]
                simp
                have h1 := BoolStep.eqConstConstTrue _ _ h (val := val)
                have hl := eval_completeness l (val := val)
                have hr := eval_completeness r (val := val)
                have h2 := BoolStepStar.eqArStepStarLeft l (ArExpr.Const (eval V val l)) r hl
                have h3 := BoolStepStar.eqArStepStarRight (ArExpr.Const (eval V val l)) r (ArExpr.Const (eval V val r)) hr
                have h4 := chasles_step_star V h2 h3
                exact chasles_step_star V h4 (step_to_stepstar V h1)

            .   replace h := eq_false_of_ne_true h
                rw [h]
                have h' := ne_of_beq_false h
                rw [<- bne_iff_ne] at h'
                have h1 := BoolStep.eqConstConstFalse _ _ h' (val := val)
                have hl := eval_completeness l (val := val)
                have hr := eval_completeness r (val := val)
                have h2 := BoolStepStar.eqArStepStarLeft l (ArExpr.Const (eval V val l)) r hl
                have h3 := BoolStepStar.eqArStepStarRight (ArExpr.Const (eval V val l)) r (ArExpr.Const (eval V val r)) hr
                have h4 := chasles_step_star V h2 h3
                exact chasles_step_star V h4 (step_to_stepstar V h1)
        | Less l r =>
            simp [eval_bool]

            by_cases h: (eval V val l < eval V val r)

            .   rw [decide_eq_true]
                have h1 := BoolStep.lessConstConstTrue _ _ h (val := val)
                have hr := eval_completeness r (val := val)
                have hl := eval_completeness l (val := val)
                have hr := eval_completeness r (val := val)
                have h2 := BoolStepStar.lessArStepStarLeft l (ArExpr.Const (eval V val l)) r hl
                have h3 := BoolStepStar.lessArStepStarRight (ArExpr.Const (eval V val l)) r (ArExpr.Const (eval V val r)) hr
                have h4 := chasles_step_star V h2 h3
                apply chasles_step_star V h4 (step_to_stepstar V h1)
                exact h

            .   rw [decide_eq_false]
                have h' := h
                rw [Int.not_lt] at h'
                rw [<- ge_iff_le] at h'
                have h1 := BoolStep.lessConstConstFalse _ _ h' (val := val)
                have hl := eval_completeness l (val := val)
                have hr := eval_completeness r (val := val)
                have h2 := BoolStepStar.lessArStepStarLeft l (ArExpr.Const (eval V val l)) r hl
                have h3 := BoolStepStar.lessArStepStarRight (ArExpr.Const (eval V val l)) r (ArExpr.Const (eval V val r)) hr
                have h4 := chasles_step_star V h2 h3
                exact chasles_step_star V h4 (step_to_stepstar V h1)
                exact h
end
