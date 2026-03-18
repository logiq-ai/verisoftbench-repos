variable (V: Type)

mutual
    -- Arithmetic Expressions

    inductive ArExpr: Type
        | Const: Int -> ArExpr
        | Add: ArExpr -> ArExpr -> ArExpr
        | Sub: ArExpr -> ArExpr -> ArExpr
        | Mul: ArExpr -> ArExpr -> ArExpr
        | Var: V -> ArExpr
        | If : BoolExpr -> ArExpr -> ArExpr -> ArExpr

    -- Boolean Expressions

    inductive BoolExpr : Type
        | Const: Bool -> BoolExpr
        | Less: ArExpr -> ArExpr -> BoolExpr
        | Eq: ArExpr -> ArExpr -> BoolExpr
        | Not : BoolExpr -> BoolExpr
        | And : BoolExpr -> BoolExpr -> BoolExpr
        | Or : BoolExpr -> BoolExpr -> BoolExpr

end

def StepKind (V: Type) (ExprType: Type):= (V -> Int) -> ExprType -> ExprType -> Prop

inductive StepStar {ExprType: Type} {Step: StepKind V ExprType} : (val: V -> Int) -> ExprType -> ExprType -> Prop where
        | refl val e : StepStar val e e
        | trans e₁ e₂ e₃ : Step val e₁ e₂ -> StepStar val e₂ e₃ -> StepStar val e₁ e₃

theorem chasles_step_star {ExprKind: Type} {Step: StepKind V ExprKind} {e₁ e₂ e₃: ExprKind}:
    StepStar (Step := Step) V val e₁ e₂  ->
        StepStar (Step := Step) V val e₂ e₃ ->
            StepStar (Step := Step) V val e₁ e₃ := by
    intros h1 h2
    induction h1 with
    | refl e => exact h2
    | trans a b c step _ ihn =>
        have h3 := ihn h2
        have h4 := StepStar.trans _ _ _ step h3
        exact h4

theorem step_to_stepstar {ExprKind: Type} {Step: StepKind V ExprKind} {e e': ExprKind}:
    Step val e e' -> StepStar (Step := Step) V val e e' := by
    intro h
    have h': StepStar (Step := Step) V val e' e' := StepStar.refl val e'
    apply StepStar.trans _ _ _ h h'

mutual
    def eval_bool (val: V -> Int) (e: BoolExpr V): Bool :=
        match e with
        | BoolExpr.Const b => b
        | BoolExpr.Less l r =>  (eval val l) < (eval val r)
        | BoolExpr.Eq l r => (eval val l) == (eval val r)
        | BoolExpr.Not e => not (eval_bool val e)
        | BoolExpr.And l r => if eval_bool val l then eval_bool val r else false
        | BoolExpr.Or l r => if eval_bool val l then true else eval_bool val r

    def eval (val: V -> Int) (e: ArExpr V) : Int :=
        match e with
            | ArExpr.Const x => x
            | ArExpr.Add lhs rhs => (eval val lhs) + (eval val rhs)
            | ArExpr.Sub lhs rhs => (eval val lhs) - (eval val rhs)
            | ArExpr.Mul lhs rhs => (eval val lhs) * (eval val rhs)
            | ArExpr.Var v => val v
            | ArExpr.If cond then_e else_e => if eval_bool val cond then eval val then_e else eval val else_e
end
