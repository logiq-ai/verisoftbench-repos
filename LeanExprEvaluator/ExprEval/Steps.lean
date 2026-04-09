import ExprEval.Expr

variable (V: Type)

-- Small steps semantic for arithmetic expressions
mutual
inductive ArStep: (val: V -> Int) -> (ArExpr V) -> (ArExpr V) -> Prop where
    | getVarValue (var: V) :
        ArStep
            val
            (ArExpr.Var var)
            (ArExpr.Const (val var))
    | addConstConst(n₁ n₂: Int) :
        ArStep
            val
            (ArExpr.Add (ArExpr.Const n₁) (ArExpr.Const n₂))
            (ArExpr.Const (n₁ + n₂))
    | subConstConst(n₁ n₂: Int) :
        ArStep
            val
            (ArExpr.Sub (ArExpr.Const n₁) (ArExpr.Const n₂))
            (ArExpr.Const (n₁ - n₂))
    | mulConstConst(n₁ n₂: Int) :
        ArStep
            val
            (ArExpr.Mul (ArExpr.Const n₁) (ArExpr.Const n₂))
            (ArExpr.Const (n₁ * n₂))
    | addLeft (e₁ e₁' e₂) : ArStep val e₁ e₁' -> ArStep val (ArExpr.Add e₁ e₂) (ArExpr.Add e₁' e₂)

    | subLeft (e₁ e₁' e₂) : ArStep val e₁ e₁' -> ArStep val (ArExpr.Sub e₁ e₂) (ArExpr.Sub e₁' e₂)

    | mulLeft (e₁ e₁' e₂) : ArStep val e₁ e₁' -> ArStep val (ArExpr.Mul e₁ e₂) (ArExpr.Mul e₁' e₂)

    | addRight (n: Int) (e₂ e₂': ArExpr V) : ArStep val e₂ e₂' -> ArStep val (ArExpr.Add (ArExpr.Const n) e₂)  (ArExpr.Add (ArExpr.Const n) e₂')

    | subRight (n: Int) (e₂ e₂': ArExpr V) : ArStep val e₂ e₂' -> ArStep val (ArExpr.Sub (ArExpr.Const n) e₂)  (ArExpr.Sub (ArExpr.Const n) e₂')
    | mulRight (n: Int) (e₂ e₂': ArExpr V) : ArStep val e₂ e₂' -> ArStep val (ArExpr.Mul (ArExpr.Const n) e₂)  (ArExpr.Mul (ArExpr.Const n) e₂')

    | ifStep (e e': BoolExpr V) (a b : ArExpr V): BoolStep val e e' ->
        ArStep val (ArExpr.If e a b) (ArExpr.If e' a b)
    | ifCondTrue (a b: ArExpr V) : ArStep val (ArExpr.If (BoolExpr.Const true) a b) a
    | ifCondFalse (a b: ArExpr V) : ArStep val (ArExpr.If (BoolExpr.Const false) a b) b

inductive BoolStep: (val: V -> Int) -> (BoolExpr V) -> (BoolExpr V) -> Prop where
    | notIsBoolNot (b: Bool): BoolStep val
        (BoolExpr.Not (BoolExpr.Const b))
        (BoolExpr.Const !b)
    | andLeftTrue (e: BoolExpr V): BoolStep val
        (BoolExpr.And (BoolExpr.Const true) e)
        e
    | orLeftFalse (e: BoolExpr V): BoolStep val
        (BoolExpr.Or (BoolExpr.Const false) e)
        e
    | andLeftShortCircuit e : BoolStep val
        (BoolExpr.And (BoolExpr.Const false) e)
        (BoolExpr.Const false)
    | orLeftShortCircuit e : BoolStep val
        (BoolExpr.Or (BoolExpr.Const true) e)
        (BoolExpr.Const true)
    | lessConstConstTrue n₁ n₂ : n₁ < n₂ -> BoolStep val
        (BoolExpr.Less (ArExpr.Const n₁) (ArExpr.Const n₂))
        (BoolExpr.Const true)
    | lessConstConstFalse n₁ n₂ : n₁ >= n₂ -> BoolStep val
        (BoolExpr.Less (ArExpr.Const n₁) (ArExpr.Const n₂))
        (BoolExpr.Const false)
    | eqConstConstTrue n₁ n₂ : n₁ = n₂ -> BoolStep val
        (BoolExpr.Eq (ArExpr.Const n₁) (ArExpr.Const n₂))
        (BoolExpr.Const true)
    | eqConstConstFalse n₁ n₂ : n₁ != n₂ -> BoolStep val
        (BoolExpr.Eq (ArExpr.Const n₁) (ArExpr.Const n₂))
        (BoolExpr.Const false)
    | lessArStepLeft (e₁ e₁' e₂: ArExpr V):
        ArStep val e₁ e₁' ->
            BoolStep val
                (BoolExpr.Less e₁ e₂)
                (BoolExpr.Less e₁' e₂)
    | eqArStepLeft (e₁ e₁' e₂: ArExpr V):
        ArStep val e₁ e₁' ->
            BoolStep val
                (BoolExpr.Eq e₁ e₂)
                (BoolExpr.Eq e₁' e₂)
     | lessArStepRight (e₁ e₂ e₂': ArExpr V):
        ArStep val e₂ e₂' ->
            BoolStep val
                (BoolExpr.Less e₁ e₂)
                (BoolExpr.Less e₁ e₂')
    | eqArStepRight (e₁ e₂ e₂': ArExpr V):
        ArStep val e₂ e₂' ->
            BoolStep val
                (BoolExpr.Eq e₁ e₂)
                (BoolExpr.Eq e₁ e₂')
    | orStepLeft (e₁ e₁' e₂: BoolExpr V):
        BoolStep val e₁ e₁' ->
            BoolStep val
                (BoolExpr.Or e₁ e₂)
                (BoolExpr.Or e₁' e₂)
    | andStepLeft (e₁ e₁' e₂: BoolExpr V):
        BoolStep val e₁ e₁' ->
            BoolStep val
                (BoolExpr.And e₁ e₂)
                (BoolExpr.And e₁' e₂)
    | notStep (e e' : BoolExpr V):
        BoolStep val e e' -> BoolStep val
            (BoolExpr.Not e)
            (BoolExpr.Not e')
end

def ArStepStar (V: Type) := StepStar (Step := ArStep V) V
def ArStepStar.refl {V: Type} (val: V -> Int) := StepStar.refl (Step := ArStep V) val
def ArStepStar.trans {V: Type} {val: V -> Int} e₁ e₂ e₃ := StepStar.trans e₁ e₂ e₃ (Step := ArStep V) (val := val)

def BoolStepStar (V: Type) := StepStar (Step := BoolStep V) V
def BoolStepStar.refl {V: Type} (val: V -> Int) := StepStar.refl (Step := BoolStep V) val
def BoolStepStar.trans {V: Type} {val: V -> Int} e₁ e₂ e₃ := StepStar.trans e₁ e₂ e₃ (Step := BoolStep V) (val := val)
