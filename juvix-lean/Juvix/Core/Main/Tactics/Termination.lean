
import Juvix.Core.Main.Tactics.Base

namespace Juvix.Core.Main

lemma Termination.var {env name i v} :
  env[i]? = some (Object.value v) →
  env ⊢ Expr.var name i ↓ := by
  intro h
  constructor
  apply Juvix.Core.Main.Eval.var
  assumption

lemma Termination.var_rec {env name i env' e} :
    env[i]? = some (Object.delayed env' e) →
    env' ⊢ e ↓ →
    env ⊢ (Expr.var name i) ↓ := by
  intro h₁ ⟨w, h₂⟩
  constructor
  apply Juvix.Core.Main.Eval.var_rec
  · assumption
  · assumption

lemma Termination.unit {env} :
  env ⊢ Expr.unit ↓ := by
  constructor
  apply Juvix.Core.Main.Eval.unit

lemma Termination.const {env c} :
  env ⊢ Expr.const c ↓ := by
  constructor
  apply Juvix.Core.Main.Eval.const

lemma Termination.constr {env nm} :
  env ⊢ Expr.constr nm ↓ := by
  constructor
  apply Juvix.Core.Main.Eval.constr

lemma Termination.app {env e₁ e₂ v env' body} :
  env ⊢ e₁ ↦ Value.closure env' body →
  env ⊢ e₂ ↦ v →
  v ∷ env' ⊢ body ↓ →
  env ⊢ Expr.app e₁ e₂ ↓ := by
  intro h₁ h₂ ⟨w, h₃⟩
  constructor
  apply Juvix.Core.Main.Eval.app <;> assumption

lemma Termination.constr_app {env e₁ e₂ e₁₁ e₁₂} :
  env ⊢ e₁ ↦ Value.constr_app e₁₁ e₁₂ →
  env ⊢ e₂ ↓ →
  env ⊢ Expr.constr_app e₁ e₂ ↓ := by
  intro h₁ h₂
  obtain ⟨v, _⟩ := h₂
  constructor
  constructor
  · assumption
  · assumption

lemma Termination.binop {env op e₁ e₂ c₁ c₂} :
  env ⊢ e₁ ↦ Value.const (Constant.int c₁) →
  env ⊢ e₂ ↦ Value.const (Constant.int c₂) →
  env ⊢ Expr.binop op e₁ e₂ ↓ := by
  intro h₁ h₂
  constructor
  apply Juvix.Core.Main.Eval.binop
  · assumption
  · assumption

lemma Termination.lambda {env name e} : env ⊢ Expr.lambda name e ↓ := by
  constructor
  apply Juvix.Core.Main.Eval.lambda

lemma Termination.save {env name e₁ e₂ v} :
  env ⊢ e₁ ↦ v →
  v ∷ env ⊢ e₂ ↓ →
  env ⊢ Expr.save name e₁ e₂ ↓ := by
  intro h₁ ⟨w, h₂⟩
  constructor
  apply Juvix.Core.Main.Eval.save
  · assumption
  · assumption

lemma Termination.branch_matches {env name vnames args_rev e e'} :
  args_rev.map Object.value ++ env ⊢ e ↓ →
  Value.constr_app name args_rev ∷ env ⊢ Expr.branch name vnames e e' ↓ := by
  intro h
  obtain ⟨w, h⟩ := h
  constructor
  apply Juvix.Core.Main.Eval.branch_matches
  assumption

lemma Termination.branch_fails {env name name' vnames args_rev e e'} :
  name ≠ name' →
  Value.constr_app name args_rev ∷ env ⊢ e' ↓ →
  Value.constr_app name args_rev ∷ env ⊢ Expr.branch name' vnames e e' ↓ := by
  intro h₁ ⟨w, h₂⟩
  constructor
  apply Juvix.Core.Main.Eval.branch_fails <;> assumption

lemma Termination.recur {env name e} :
  Object.delayed env (Expr.recur name e) :: env ⊢ e ↓ →
  env ⊢ Expr.recur name e ↓ := by
  unfold Eval.Defined
  intro h
  obtain ⟨w, h⟩ := h
  exists w
  · apply Juvix.Core.Main.Eval.recur
    exact h

macro "prove_termination" : tactic => `(tactic| repeat' (first
  | apply Termination.var
  | apply Termination.recur
  | apply Termination.lambda
  | apply Termination.constr
  | apply Termination.const
  | apply Termination.unit
  | refine Termination.app (by repeat trivial) (by repeat trivial) ?_
  | refine Termination.binop (by repeat trivial) (by repeat trivial) ?_
  | refine Termination.save (by repeat trivial) ?_
  | apply Termination.branch_matches
  | refine Termination.branch_fails (by repeat trivial) ?_ ?_
  | refine Termination.constr_app (by repeat constructor) ?_))

end Juvix.Core.Main
