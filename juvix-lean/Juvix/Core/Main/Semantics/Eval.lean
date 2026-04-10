
import Juvix.Core.Main.Language
import Mathlib.Tactic.CC

namespace Juvix.Core.Main

def eval_binop_int (op : BinaryOp) (i₁ i₂ : Int) : Int :=
  match op with
  | BinaryOp.add_int => i₁ + i₂
  | BinaryOp.sub_int => i₁ - i₂
  | BinaryOp.mul_int => i₁ * i₂
  | BinaryOp.div_int => i₁ / i₂

@[aesop unsafe constructors]
inductive Eval : Env → Expr → Value → Prop where
  | var {env name idx val} :
    env[idx]? = some (Object.value val) →
    Eval env (Expr.var name idx) val
  | var_rec {env name idx env' expr val} :
    env[idx]? = some (Object.delayed env' expr) →
    Eval env' expr val →
    Eval env (Expr.var name idx) val
  | unit {env} :
    Eval env Expr.unit Value.unit
  | const {env c} :
    Eval env (Expr.const c) (Value.const c)
  | constr {env name} :
    Eval env (Expr.constr name) (Value.constr_app name [])
  | app {env env' f body arg val val'} :
    Eval env f (Value.closure env' body) →
    Eval env arg val →
    Eval (val ∷ env') body val' →
    Eval env (Expr.app f arg) val'
  | constr_app {env ctr ctr_name ctr_args_rev arg val} :
    Eval env ctr (Value.constr_app ctr_name ctr_args_rev) →
    Eval env arg val →
    Eval env (Expr.constr_app ctr arg) (Value.constr_app ctr_name (val :: ctr_args_rev))
  | binop {env op arg₁ arg₂ val₁ val₂} :
    Eval env arg₁ (Value.const (Constant.int val₁)) →
    Eval env arg₂ (Value.const (Constant.int val₂)) →
    Eval env (Expr.binop op arg₁ arg₂) (Value.const (Constant.int (eval_binop_int op val₁ val₂)))
  | lambda {env name body} :
    Eval env (Expr.lambda name body) (Value.closure env body)
  | save {env name value body val val'} :
    Eval env value val →
    Eval (val ∷ env) body val' →
    Eval env (Expr.save name value body) val'
  | branch_matches {env name args_rev body val} :
    Eval (args_rev.map Object.value ++ env) body val →
    Eval (Value.constr_app name args_rev ∷ env) (Expr.branch name _ body _) val
  | branch_fails {env name name' args_rev next val} :
    name ≠ name' →
    Eval (Value.constr_app name args_rev ∷ env) next val →
    Eval (Value.constr_app name args_rev ∷ env) (Expr.branch name' _ _ next) val
  | recur {env name body val} :
    Eval (Object.delayed env (Expr.recur name body) :: env) body val →
    Eval env (Expr.recur name body) val

notation:40 env:40 " ⊢ " e:40 " ↦ " v:40 => Eval env e v

def Eval.Defined (env : Env) (e : Expr) : Prop :=
  ∃ v, env ⊢ e ↦ v

notation:40 env:40 " ⊢ " e:40 " ↓" => Eval.Defined env e

-- The evaluation relation is deterministic.
theorem Eval.deterministic {env e v₁ v₂} (h₁ : env ⊢ e ↦ v₁) (h₂ : env ⊢ e ↦ v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | var =>
    cases h₂ <;> cc
  | var_rec =>
    cases h₂ <;> aesop
  | const =>
    cases h₂; cc
  | constr =>
    cases h₂; cc
  | app _ _ _ ih ih' aih =>
    cases h₂ with
    | app hval harg =>
      apply aih
      specialize (ih hval)
      specialize (ih' harg)
      simp_all
  | constr_app _ _ ih ih' =>
    cases h₂ with
    | constr_app hctr harg =>
      specialize (ih hctr)
      specialize (ih' harg)
      simp_all
  | binop _ _ ih₁ ih₂ =>
    cases h₂ with
    | binop h₁ h₂ =>
      specialize (ih₁ h₁)
      specialize (ih₂ h₂)
      simp_all
  | lambda =>
    cases h₂; cc
  | save _ _ ih ih' =>
    cases h₂ with
    | save hval hbody =>
      specialize (ih hval)
      rw [<- ih] at hbody
      specialize (ih' hbody)
      simp_all
  | branch_matches _ ih =>
    specialize (@ih v₂)
    cases h₂ <;> cc
  | branch_fails _ _ ih =>
    specialize (@ih v₂)
    cases h₂ <;> cc
  | unit =>
    cases h₂; cc
  | recur h ih =>
    cases h₂ with
    | recur h =>
      specialize (ih h)
      simp_all

end Juvix.Core.Main
