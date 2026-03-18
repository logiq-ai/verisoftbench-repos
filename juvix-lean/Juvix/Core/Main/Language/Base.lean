
import Mathlib.Data.String.Basic

namespace Juvix.Core.Main

abbrev Name : Type := String

inductive Constant : Type where
  | int : Int → Constant
  | string : String → Constant
  deriving Inhabited, BEq, DecidableEq

inductive BinaryOp : Type where
  | add_int : BinaryOp
  | sub_int : BinaryOp
  | mul_int : BinaryOp
  | div_int : BinaryOp
  deriving Inhabited, BEq, DecidableEq

-- The names of variables are purely decorative and are not used in the
-- semantics. The variables are uniquely identifed by their de Bruijn indices.
inductive Expr : Type where
  | var : (name : String) → (index : Nat) → Expr
  | unit : Expr
  | const : Constant → Expr
  | constr : Name → Expr
  | app : Expr → Expr → Expr
  | constr_app : Expr → Expr → Expr
  | binop : (oper : BinaryOp) → (arg₁ arg₂ : Expr) → Expr
  | lambda : (var_name : String) → (body : Expr) → Expr
  | save : (var_name : String) → (value : Expr) → (body : Expr) → Expr
  | branch : (constr : Name) → (var_names : List Name) → (body : Expr) → (next : Expr) → Expr
  | recur : (var_name : Name) → (body : Expr) → Expr
  | fail : Expr
  deriving Inhabited, BEq, DecidableEq

infixl:100 " @@ " => Expr.app

def Expr.mk_app (f : Expr) : List Expr → Expr
  | [] => f
  | x :: xs => Expr.mk_app (Expr.app f x) xs

end Juvix.Core.Main
