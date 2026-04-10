
import Juvix.Core.Main.Semantics.Eval
import Mathlib.Tactic.Linarith

namespace Juvix.Core.Main

inductive Eval.Indexed : Nat → Env → Expr → Value → Prop where
  | var {n env name idx val} :
    env[idx]? = some (Object.value val) →
    Eval.Indexed n env (Expr.var name idx) val
  | var_rec {n env name idx env' expr val} :
    env[idx]? = some (Object.delayed env' expr) →
    Eval.Indexed n env' expr val →
    Eval.Indexed n env (Expr.var name idx) val
  | unit {n env} :
    Eval.Indexed n env Expr.unit Value.unit
  | const {n env c} :
    Eval.Indexed n env (Expr.const c) (Value.const c)
  | constr {n env name} :
    Eval.Indexed n env (Expr.constr name) (Value.constr_app name [])
  | app {n n₁ n₂ env env' f body arg val val'} :
    n₁ + n₂ + 1 ≤ n →
    Eval.Indexed n₁ env f (Value.closure env' body) →
    Eval.Indexed (n₁ + 1) env arg val →
    Eval.Indexed n₂ (val ∷ env') body val' →
    Eval.Indexed n env (Expr.app f arg) val'
  | constr_app {n n' env ctr ctr_name ctr_args_rev arg val} :
    n' < n →
    Eval.Indexed n env ctr (Value.constr_app ctr_name ctr_args_rev) →
    Eval.Indexed n' env arg val →
    Eval.Indexed n env (Expr.constr_app ctr arg) (Value.constr_app ctr_name (val :: ctr_args_rev))
  | binop {n env op arg₁ arg₂ val₁ val₂} :
    Eval.Indexed n env arg₁ (Value.const (Constant.int val₁)) →
    Eval.Indexed n env arg₂ (Value.const (Constant.int val₂)) →
    Eval.Indexed n env (Expr.binop op arg₁ arg₂) (Value.const (Constant.int (eval_binop_int op val₁ val₂)))
  | lambda {n env name body} :
    Eval.Indexed n env (Expr.lambda name body) (Value.closure env body)
  | save {n n₁ n₂ env name value body val val'} :
    n₁ + n₂ ≤ n →
    Eval.Indexed n₁ env value val →
    Eval.Indexed n₂ (val ∷ env) body val' →
    Eval.Indexed n env (Expr.save name value body) val'
  | branch_matches {n n' env name args_rev body val} :
    n' < n →
    Eval.Indexed n' (args_rev.map Object.value ++ env) body val →
    Eval.Indexed n (Value.constr_app name args_rev ∷ env) (Expr.branch name _ body _) val
  | branch_fails {n env name name' args_rev next val} :
    name ≠ name' →
    Eval.Indexed n (Value.constr_app name args_rev ∷ env) next val →
    Eval.Indexed n (Value.constr_app name args_rev ∷ env) (Expr.branch name' _ _ next) val
  | recur {n n' env name body val} :
    n' < n →
    Eval.Indexed n' (Object.delayed env (Expr.recur name body) :: env) body val →
    Eval.Indexed n env (Expr.recur name body) val

notation:40 env:40 " ⊢ " e:40 " ↦(" n ") " v:40 => Eval.Indexed n env e v

lemma Eval.Indexed.monotone {n n' env e v} (h : env ⊢ e ↦(n) v) (h' : n ≤ n') : env ⊢ e ↦(n') v := by
  induction h generalizing n'
  case var =>
    constructor; assumption
  case var_rec h =>
    apply Eval.Indexed.var_rec
    · assumption
    · apply h; assumption
  case unit =>
    constructor
  case const =>
    constructor
  case constr =>
    constructor
  case app n n₁ n₂ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ ih₃ =>
    have hn : n₁ + n₂ + 1 ≤ n' := by linarith
    apply Eval.Indexed.app
    · exact hn
    · apply ih₁; linarith
    · apply ih₂; linarith
    · apply ih₃; linarith
  case constr_app n n₁ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    have hn : n₁ < n' := by linarith
    apply Eval.Indexed.constr_app
    · exact hn
    · apply ih₁; linarith
    · apply ih₂; linarith
  case binop ih₁ ih₂ =>
    apply Eval.Indexed.binop
    · apply ih₁; assumption
    · apply ih₂; assumption
  case lambda =>
    constructor
  case save n n₁ n₂ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    have hn : n₁ + n₂ ≤ n' := by linarith
    apply Eval.Indexed.save
    · exact hn
    · apply ih₁; linarith
    · apply ih₂; linarith
  case branch_matches _ n₁ n₁' _ _ _ _ _ _ _ ih =>
    apply Eval.Indexed.branch_matches (n' := n₁')
    · linarith
    · apply ih; rfl
  case branch_fails ih =>
    apply Eval.Indexed.branch_fails
    · assumption
    · apply ih; assumption
  case recur n₁ n₂ _ _ _ _ _ _ ih =>
    apply Eval.Indexed.recur (n' := n₂)
    · linarith
    · apply ih; rfl

lemma Eval.Indexed.toEval {n env e v} (h : env ⊢ e ↦(n) v) : env ⊢ e ↦ v := by
  induction h
  case var =>
    constructor; assumption
  case var_rec =>
    apply Eval.var_rec <;> assumption
  case unit =>
    constructor
  case const =>
    constructor
  case constr =>
    constructor
  case app =>
    apply Eval.app <;> assumption
  case constr_app =>
    apply Eval.constr_app <;> assumption
  case binop =>
    apply Eval.binop <;> assumption
  case lambda =>
    constructor
  case save =>
    apply Eval.save <;> assumption
  case branch_matches =>
    apply Eval.branch_matches; assumption
  case branch_fails =>
    apply Eval.branch_fails <;> assumption
  case recur =>
    apply Eval.recur; assumption

lemma Eval.toIndexed {env e v} (h : env ⊢ e ↦ v) : ∃ n, env ⊢ e ↦(n) v := by
  induction h
  case var =>
    exists 0; apply Eval.Indexed.var; assumption
  case var_rec ih =>
    obtain ⟨n, ih⟩ := ih
    exists n
    apply Eval.Indexed.var_rec <;> assumption
  case unit =>
    exists 0; apply Eval.Indexed.unit
  case const =>
    exists 0; apply Eval.Indexed.const
  case constr =>
    exists 0; apply Eval.Indexed.constr
  case app env env' f body arg val val' _ _ _ ih1 ih2 ih3 =>
    obtain ⟨n₁, ih₁⟩ := ih1
    obtain ⟨n₂, ih₂⟩ := ih2
    obtain ⟨n₃, ih₃⟩ := ih3
    have ih₁' : env ⊢ f ↦(n₁ + n₂) Value.closure env' body := by
      apply Eval.Indexed.monotone ih₁; linarith
    have ih₂' : env ⊢ arg ↦(n₁ + n₂ + 1) val := by
      apply Eval.Indexed.monotone ih₂; linarith
    exists (n₁ + n₂ + n₃ + 1)
    apply Eval.Indexed.app
    · rfl
    · exact ih₁'
    · exact ih₂'
    · exact ih₃
  case constr_app ih₁ ih₂ =>
    obtain ⟨n₁, ih₁⟩ := ih₁
    obtain ⟨n₂, ih₂⟩ := ih₂
    exists (n₁ + n₂ + 1)
    apply Eval.Indexed.constr_app (n' := n₁ + n₂)
    · linarith
    · apply Eval.Indexed.monotone ih₁; linarith
    · apply Eval.Indexed.monotone ih₂; linarith
  case binop ih₁ ih₂ =>
    obtain ⟨n₁, ih₁⟩ := ih₁
    obtain ⟨n₂, ih₂⟩ := ih₂
    exists (n₁ + n₂)
    apply Eval.Indexed.binop (n := n₁ + n₂)
    · apply Eval.Indexed.monotone ih₁; linarith
    · apply Eval.Indexed.monotone ih₂; linarith
  case lambda =>
    exists 0; apply Eval.Indexed.lambda
  case save ih₁ ih₂ =>
    obtain ⟨n₁, ih₁⟩ := ih₁
    obtain ⟨n₂, ih₂⟩ := ih₂
    exists (n₁ + n₂)
    apply Eval.Indexed.save (n := n₁ + n₂)
    · rfl
    · apply Eval.Indexed.monotone ih₁; linarith
    · apply Eval.Indexed.monotone ih₂; linarith
  case branch_matches ih =>
    obtain ⟨n, ih⟩ := ih
    exists (n + 1)
    apply Eval.Indexed.branch_matches (n' := n)
    · linarith
    · assumption
  case branch_fails ih =>
    obtain ⟨n, ih⟩ := ih
    exists n
    apply Eval.Indexed.branch_fails <;> assumption
  case recur ih =>
    obtain ⟨n, ih⟩ := ih
    exists n.succ
    apply Eval.Indexed.recur (n' := n)
    · linarith
    · assumption

end Juvix.Core.Main
