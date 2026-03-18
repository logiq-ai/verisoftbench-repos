
import Juvix.Core.Main.Language.Base

namespace Juvix.Core.Main

-- A context is an expression with exactly one hole.
inductive Context : Type where
  | hole : Context
  | app_left : Context → Expr → Context
  | app_right : Expr → Context → Context
  | constr_app_left : Context → Expr → Context
  | constr_app_right : Expr → Context → Context
  | binop_left : (oper : BinaryOp) → (arg₁ : Context) → (arg₂ : Expr) → Context
  | binop_right : (oper : BinaryOp) → (arg₁ : Expr) → (arg₂ : Context) → Context
  | lambda : (var_name : String) → (body : Context) → Context
  | save_left : (var_name : String) → (value : Context) → (body : Expr) → Context
  | save_right : (var_name : String) → (value : Expr) → (body : Context) → Context
  | branch_left : (constr : Name) → (var_names : List Name) → (body : Context) → (next : Expr) → Context
  | branch_right : (constr : Name) → (var_names : List Name) → (body : Expr) → (next : Context) → Context
  | recur : (var_name : Name) → (ctx : Context) → Context
  deriving Inhabited, BEq

@[simp]
def Context.subst (C : Context) (e : Expr) : Expr :=
  match C with
  | Context.hole => e
  | Context.app_left C' e' => Expr.app (C'.subst e) e'
  | Context.app_right e' C' => Expr.app e' (C'.subst e)
  | Context.constr_app_left C' e' => Expr.constr_app (C'.subst e) e'
  | Context.constr_app_right e' C' => Expr.constr_app e' (C'.subst e)
  | Context.binop_left oper C₁ e₂ => Expr.binop oper (C₁.subst e) e₂
  | Context.binop_right oper e₁ C₂ => Expr.binop oper e₁ (C₂.subst e)
  | Context.lambda s C' => Expr.lambda s (C'.subst e)
  | Context.save_left s C' e' => Expr.save s (C'.subst e) e'
  | Context.save_right s e' C' => Expr.save s e' (C'.subst e)
  | Context.branch_left constr names C' next => Expr.branch constr names (C'.subst e) next
  | Context.branch_right constr names body C' => Expr.branch constr names body (C'.subst e)
  | Context.recur name C' => Expr.recur name (C'.subst e)

end Juvix.Core.Main
