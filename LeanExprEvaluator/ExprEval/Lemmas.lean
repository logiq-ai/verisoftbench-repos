import ExprEval.Expr
import ExprEval.Steps
mutual

    theorem arstep_preserve_eval (e e': ArExpr V): (ArStep V val) e e' -> eval V val e = eval V val e' := by
            intro h
            cases h with

            | addConstConst n₁ n₂
            | subConstConst n₁ n₂
            | mulConstConst n₁ n₂ => simp [eval]
            | subLeft e₁ e₁' e₂ step
            | addLeft e₁ e₁' e₂ step =>
                simp [eval]
                exact arstep_preserve_eval e₁ e₁' step
            | mulLeft e₁ e₁' e₂ step =>
                simp [eval]
                cases h : (eval V val e₂ == 0)
                .   rw [beq_eq_false_iff_ne] at h
                    rw [Int.mul_eq_mul_right_iff]
                    exact arstep_preserve_eval e₁ e₁' step
                    exact h
                .   rw [beq_iff_eq] at h
                    rw [h]
                    simp
            | addRight n e₂ e₁' step
            | subRight n e₂ e₁' step
            | mulRight n e₂ e₁' step =>
                -- have ih := arstep_preserve_eval e₁ e₁' step
                have ihn := arstep_preserve_eval e₂ e₁' step
                simp [eval, ihn]

            | getVarValue var => simp [eval]
            | ifCondTrue a b =>
                simp [eval]
                simp [eval_bool]
            | ifCondFalse a b =>
                simp [eval]
                simp [eval_bool]
            | ifStep e e' a b bstep =>
                have ihn := boolstep_preserves_eval_bool e e' bstep
                cases h: (eval_bool V val e)
                .   simp [eval]
                    rw [h]
                    rw [<- ihn]
                    simp
                    intro noth
                    rw [h] at noth
                    nomatch noth
                .   simp [eval]
                    rw [h]
                    rw [<- ihn]
                    simp
                    intro noth
                    rw [h] at noth
                    nomatch noth

    theorem arstepstar_preserves_eval (e e': ArExpr V) :
            ArStepStar V val e e' -> eval V val e = eval V val e' := by
            intro h
            induction h with
            | refl _ => rfl
            | trans _ _ _ h1 _ ih =>
                rw [arstep_preserve_eval _ _ h1, ih]

    theorem arstepstar_add_left (e₁ e₁' e₂: ArExpr V) :
            ArStepStar V val e₁ e₁' -> ArStepStar V val (ArExpr.Add e₁ e₂) (ArExpr.Add e₁' e₂) := by
            intro h
            induction h with
            | refl _ => apply StepStar.refl
            | trans _ _ _ step _ ih =>
                    apply StepStar.trans
                    . exact ArStep.addLeft _ _ _ step
                    . exact ih

    theorem arstepstar_add_right (n: Int) (e₂ e₂': ArExpr V) :
            ArStepStar V val e₂ e₂' ->
                    ArStepStar V val
                            (ArExpr.Add (ArExpr.Const n) e₂)
                            (ArExpr.Add (ArExpr.Const n) e₂') := by
            intro h
            induction h with
            | refl _ => apply StepStar.refl
            | trans e₁ e₂ e3 step1 step2 ih =>
                    apply StepStar.trans
                    . apply ArStep.addRight _ _ _ step1
                    . exact ih

    theorem arstepstar_sub_left (e₁ e₁' e₂: ArExpr V) :
            ArStepStar V val e₁ e₁' ->
                    ArStepStar V val
                            (ArExpr.Sub e₁ e₂)
                            (ArExpr.Sub e₁' e₂) := by
            intro h
            induction h with
            | refl _ => apply StepStar.refl
            | trans _ _ _ step _ ih =>
                    apply StepStar.trans
                    . exact ArStep.subLeft _ _ _ step
                    . exact ih

    theorem arstepstar_sub_right (n: Int) (e₂ e₂': ArExpr V) :
            ArStepStar V val e₂ e₂' ->
                    ArStepStar V val
                            (ArExpr.Sub (ArExpr.Const n) e₂)
                            (ArExpr.Sub (ArExpr.Const n) e₂') := by
            intro h
            induction h with
            | refl _ => apply StepStar.refl
            | trans e₁ e₂ e3 step1 step2 ih =>
                    apply StepStar.trans
                    . apply ArStep.subRight _ _ _ step1
                    . exact ih

    theorem arstepstar_mul_left (e₁ e₁' e₂: ArExpr V) :
            ArStepStar V val e₁ e₁' ->
                    ArStepStar V val
                            (ArExpr.Mul e₁ e₂)
                            (ArExpr.Mul e₁' e₂) := by
            intro h
            induction h with
            | refl _ => apply StepStar.refl
            | trans _ _ _ step _ ih =>
                    apply StepStar.trans
                    . exact ArStep.mulLeft _ _ _ step
                    . exact ih

    theorem arstepstar_mul_right (n: Int) (e₂ e₂': ArExpr V) :
            ArStepStar V val e₂ e₂' ->
                    ArStepStar V val
                            (ArExpr.Mul (ArExpr.Const n) e₂)
                            (ArExpr.Mul (ArExpr.Const n) e₂') := by
            intro h
            induction h with
            | refl _ => apply StepStar.refl
            | trans e₁ e₂ e3 step1 step2 ih =>
                    apply StepStar.trans
                    . apply ArStep.mulRight _ _ _ step1
                    . exact ih

    theorem ArStepStar.ifStep (e e': BoolExpr V) (a b: ArExpr V): BoolStepStar V val e e' ->
        ArStepStar V val (ArExpr.If e a b) (ArExpr.If e' a b) := by
        intro h
        induction h with
        | refl => apply StepStar.refl
        | trans e₁ e₂ e₃ step sstar ih =>
            apply StepStar.trans
            . apply ArStep.ifStep _ _ _ _ step
            . exact ih



    theorem boolstep_preserves_eval_bool (e e': BoolExpr V):
        BoolStep V val e e' -> eval_bool V val e = eval_bool V val e' := by
        intro h
        cases h with
        | notIsBoolNot b => simp [eval_bool]
        | andLeftTrue e => simp [eval_bool]
        | orLeftFalse e => simp [eval_bool]
        | andLeftShortCircuit e => simp [eval_bool]
        | orLeftShortCircuit e => simp [eval_bool]
        | lessConstConstTrue n1 n2 h =>
            simp [eval_bool]
            simp [eval]
            exact h
        | lessConstConstFalse n1 n2 h =>
            simp [eval_bool]
            simp [eval]
            exact h
        | eqConstConstTrue n1 n2 h =>
            simp [eval_bool]
            simp [eval]
            exact h
        | eqConstConstFalse n1 n2 h =>
            simp [eval_bool]
            simp [eval]
            simp [bne_iff_ne] at h
            exact h
        | lessArStepLeft e₁ e₁' e₂ arstep
        | eqArStepLeft e₁ e₁' e₂ arstep =>
            simp [eval_bool]
            have h' := arstep_preserve_eval e₁ e₁' arstep
            rw [h']
        | lessArStepRight e₁ e₂ e₂' arstep
        | eqArStepRight e₁ e₂ e₂' arstep =>
            simp [eval_bool]
            have h' := arstep_preserve_eval e₂ e₂' arstep
            rw [h']
        | orStepLeft e₁ e₁' e₂ step
        | andStepLeft e₁ e₁' e₂ step =>
            have ihn := boolstep_preserves_eval_bool e₁ e₁' step
            simp [eval_bool]
            rw [ihn]
        | notStep e e' step =>
            simp[eval_bool]
            have ihn := boolstep_preserves_eval_bool e e' step
            rw [ihn]

    theorem boolstepstar_preserves_eval_bool (e e': BoolExpr V):
        BoolStepStar V val e e' -> eval_bool V val e = eval_bool V val e' := by
        intro h
        induction h with
        | refl => rfl
        | trans _ _ _ h_step _ ihn =>
            rw [<- ihn]
            exact boolstep_preserves_eval_bool _ _ h_step

    theorem BoolStepStar.notStep {V: Type} {val: V -> Int}
        (e e': BoolExpr V):
            BoolStepStar V val e e' -> BoolStepStar V val (BoolExpr.Not e) (BoolExpr.Not e') := by
        intro h
        induction h with
        | refl => apply BoolStepStar.refl
        | trans e₁ e₂ e₃ step _ ihn =>
            have h':= BoolStep.notStep _ _ step
            apply BoolStepStar.trans _ _ _ h' ihn

    theorem BoolStepStar.andStepLeft (e₁ e₁' e₂: BoolExpr V):
        BoolStepStar V val e₁ e₁' -> BoolStepStar V val
            (BoolExpr.And e₁ e₂)
            (BoolExpr.And e₁' e₂) := by
        intro h
        induction h with
        | refl => apply BoolStepStar.refl
        | trans a b c step _ ihn =>
            have h' := BoolStep.andStepLeft (e₂ := e₂) _ _ step
            apply BoolStepStar.trans _ _ _ h' ihn

    theorem BoolStepStar.orStepLeft (e₁ e₁' e₂: BoolExpr V):
        BoolStepStar V val e₁ e₁' -> BoolStepStar V val
            (BoolExpr.Or e₁ e₂)
            (BoolExpr.Or e₁' e₂) := by
        intro h
        induction h with
        | refl => apply BoolStepStar.refl
        | trans a b c step _ ihn =>
            have h' := BoolStep.orStepLeft (e₂ := e₂) _ _ step
            apply BoolStepStar.trans _ _ _ h' ihn

    theorem BoolStepStar.eqArStepStarLeft (e₁ e₁' e₂: ArExpr V):
        ArStepStar V val e₁ e₁' ->
            BoolStepStar V val
                (BoolExpr.Eq e₁ e₂)
                (BoolExpr.Eq e₁' e₂) := by
        intro h
        induction h with
        | refl => apply BoolStepStar.refl
        | trans a b c step _ ihn =>
            have h' := BoolStep.eqArStepLeft _ _ e₂ step
            apply StepStar.trans _ _ _ h' ihn

    theorem BoolStepStar.eqArStepStarRight (e₁ e₂ e₂': ArExpr V):
        ArStepStar V val e₂ e₂' ->
            BoolStepStar V val
                (BoolExpr.Eq e₁ e₂)
                (BoolExpr.Eq e₁ e₂') := by
        intro h
        induction h with
        | refl => apply StepStar.refl
        | trans a b c step _ ihn =>
            have h' := BoolStep.eqArStepRight e₁ _ _ step
            apply StepStar.trans _ _ _ h' ihn


    theorem BoolStepStar.lessArStepStarLeft (e₁ e₁' e₂: ArExpr V):
        ArStepStar V val e₁ e₁' ->
            BoolStepStar V val
                (BoolExpr.Less e₁ e₂)
                (BoolExpr.Less e₁' e₂) := by
        intro h
        induction h with
        | refl => apply BoolStepStar.refl
        | trans a b c step _ ihn =>
            have h' := BoolStep.lessArStepLeft _ _ e₂ step
            apply StepStar.trans _ _ _ h' ihn

    theorem BoolStepStar.lessArStepStarRight (e₁ e₂ e₂': ArExpr V):
        ArStepStar V val e₂ e₂' ->
            BoolStepStar V val
                (BoolExpr.Less e₁ e₂)
                (BoolExpr.Less e₁ e₂') := by
        intro h
        induction h with
        | refl => apply StepStar.refl
        | trans a b c step _ ihn =>
            have h' := BoolStep.lessArStepRight e₁ _ _ step
            apply StepStar.trans _ _ _ h' ihn
end
