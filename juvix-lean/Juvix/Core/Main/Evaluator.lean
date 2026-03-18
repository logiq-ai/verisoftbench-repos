
import Juvix.Core.Main.Language
import Juvix.Core.Main.Semantics

namespace Juvix.Core.Main

partial def eval (env : Env) : Expr -> Value
  | Expr.var _ idx => match env[idx]! with
    | Object.value val => val
    | Object.delayed env' expr => eval env' expr
  | Expr.unit => Value.unit
  | Expr.const c => Value.const c
  | Expr.constr name => Value.constr_app name []
  | Expr.app f arg => match eval env f with
    | Value.closure env' body => eval (eval env arg ∷ env') body
    | _ => panic! "expected closure"
  | Expr.constr_app ctr arg => match eval env ctr with
    | Value.constr_app ctr_name ctr_args_rev => Value.constr_app ctr_name (eval env arg :: ctr_args_rev)
    | _ => panic! "expected constructor application"
  | Expr.binop op arg₁ arg₂ => match eval env arg₁, eval env arg₂ with
    | Value.const (Constant.int val₁), Value.const (Constant.int val₂) =>
      Value.const (Constant.int (eval_binop_int op val₁ val₂))
    | _, _ => panic! "expected integer constants"
  | Expr.lambda _ body => Value.closure env body
  | Expr.save _ value body => eval (eval env value ∷ env) body
  | Expr.branch name _ body next => match env with
    | Object.value (Value.constr_app name' args_rev) :: env' =>
      if name = name' then
        eval (args_rev.map Object.value ++ env') body
      else
        eval env next
    | _ => panic! "expected constructor application"
  | Expr.recur name body =>
    eval (Object.delayed env (Expr.recur name body) :: env) body
  | Expr.fail => panic! "evaluation failed"

end Juvix.Core.Main
