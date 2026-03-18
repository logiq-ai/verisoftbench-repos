
import Juvix.Core.Main.Semantics.Approx.Congruence
import Juvix.Core.Main.Semantics.Equiv

namespace Juvix.Core.Main

lemma Expr.Equiv.congruence {e₁ e₂} (C : Context) : e₁ ≈ e₂ → C.subst e₁ ≈ C.subst e₂ := by
  intro h
  simp_all only [Expr.Equiv]
  aesop (add unsafe Expr.Approx.congruence)

lemma Expr.Equiv.cong_app {e₁ e₂ e₁' e₂'} : e₁ ≈ e₁' → e₂ ≈ e₂' → Expr.app e₁ e₂ ≈ Expr.app e₁' e₂' := by
  simp_all only [Expr.Equiv]
  aesop (add unsafe Expr.Approx.cong_app)

lemma Expr.Equiv.cong_constr_app {e₁ e₂ e₁' e₂'} : e₁ ≈ e₁' → e₂ ≈ e₂' → Expr.constr_app e₁ e₂ ≈ Expr.constr_app e₁' e₂' := by
  simp_all only [Expr.Equiv]
  aesop (add unsafe Expr.Approx.cong_constr_app)

lemma Expr.Equiv.cong_binop {op e₁ e₂ e₁' e₂'} : e₁ ≈ e₁' → e₂ ≈ e₂' → Expr.binop op e₁ e₂ ≈ Expr.binop op e₁' e₂' := by
  simp_all only [Expr.Equiv]
  aesop (add unsafe Expr.Approx.cong_binop)

lemma Expr.Equiv.cong_lambda {name e₁ e₁'} : e₁ ≈ e₁' → Expr.lambda name e₁ ≈ Expr.lambda name e₁' := by
  simp_all only [Expr.Equiv]
  aesop (add unsafe Expr.Approx.cong_lambda)

lemma Expr.Equiv.cong_save {name e₁ e₂ e₁' e₂'} : e₁ ≈ e₁' → e₂ ≈ e₂' → Expr.save name e₁ e₂ ≈ Expr.save name e₁' e₂' := by
  simp_all only [Expr.Equiv]
  aesop (add unsafe Expr.Approx.cong_save)

lemma Expr.Equiv.cong_branch {constr names e₁ e₂ e₁' e₂'} : e₁ ≈ e₁' → e₂ ≈ e₂' → Expr.branch constr names e₁ e₂ ≈ Expr.branch constr names e₁' e₂' := by
  simp_all only [Expr.Equiv]
  aesop (add unsafe Expr.Approx.cong_branch)

lemma Expr.Equiv.cong_recur {name e e'} : e ≈ e' → Expr.recur name e ≈ Expr.recur name e' := by
  simp_all only [Expr.Equiv]
  aesop (add unsafe Expr.Approx.cong_recur)

lemma Expr.Equiv.Param.cong_var {v v' x x' env env' name name'} :
  env[x]? = some (Object.value v) →
  env'[x']? = some (Object.value v') →
  v ≈ᵥ v' →
  Expr.var name x ≈⟨env, env'⟩ Expr.var name' x' := by
  unfold Expr.Equiv.Param Value.Equiv
  aesop (add unsafe Expr.Approx.Param.cong_var)

lemma Expr.Equiv.Param.cong_unit {env env'} :
  Expr.unit ≈⟨env, env'⟩ Expr.unit := by
  unfold Expr.Equiv.Param
  aesop (add unsafe Expr.Approx.Param.cong_unit)

lemma Expr.Equiv.Param.cong_const {c env env'} :
  Expr.const c ≈⟨env, env'⟩ Expr.const c := by
  unfold Expr.Equiv.Param
  aesop (add unsafe Expr.Approx.Param.cong_const)

lemma Expr.Equiv.Param.cong_constr {name env env'} :
  Expr.constr name ≈⟨env, env'⟩ Expr.constr name := by
  unfold Expr.Equiv.Param
  aesop (add unsafe Expr.Approx.Param.cong_constr)

lemma Expr.Equiv.Param.cong_app {e₁ e₂ e₁' e₂' env env'} :
  e₁ ≈⟨env, env'⟩ e₁' →
  e₂ ≈⟨env, env'⟩ e₂' →
  Expr.app e₁ e₂ ≈⟨env, env'⟩ Expr.app e₁' e₂' := by
  unfold Expr.Equiv.Param
  aesop (add unsafe Expr.Approx.Param.cong_app)

lemma Expr.Equiv.Param.cong_constr_app {e₁ e₂ e₁' e₂' env env'} :
  e₁ ≈⟨env, env'⟩ e₁' →
  e₂ ≈⟨env, env'⟩ e₂' →
  Expr.constr_app e₁ e₂ ≈⟨env, env'⟩ Expr.constr_app e₁' e₂' := by
  unfold Expr.Equiv.Param
  aesop (add unsafe Expr.Approx.Param.cong_constr_app)

lemma Expr.Equiv.Param.cong_binop {op e₁ e₂ e₁' e₂' env env'} :
  e₁ ≈⟨env, env'⟩ e₁' →
  e₂ ≈⟨env, env'⟩ e₂' →
  Expr.binop op e₁ e₂ ≈⟨env, env'⟩ Expr.binop op e₁' e₂' := by
  unfold Expr.Equiv.Param
  aesop (add unsafe Expr.Approx.Param.cong_binop)

lemma Expr.Equiv.Param.cong_lambda {e₁ e₁' env env' name name'} :
  (∀ a₁ a₂, a₁ ≈ᵥ a₂ → e₁ ≈⟨a₁ ∷ env, a₂ ∷ env'⟩ e₁') →
  Expr.lambda name e₁ ≈⟨env, env'⟩ Expr.lambda name' e₁' := by
  unfold Expr.Equiv.Param
  intro h
  constructor
  · apply Expr.Approx.Param.cong_lambda
    intro a₁ a₂ happrox
    have h' := (h a₁ a₁ (by rfl)).left
    apply Expr.Approx.Param.preserved
    · apply h'
    · constructor
      · constructor
        assumption
      · apply Env.Approx.refl
  · apply Expr.Approx.Param.cong_lambda
    intro a₁ a₂ happrox
    have h' := (h a₁ a₁ (by rfl)).right
    apply Expr.Approx.Param.preserved
    · apply h'
    · constructor
      · constructor
        assumption
      · apply Env.Approx.refl

lemma Expr.Equiv.Param.cong_save {e₁ e₂ e₁' e₂' env env' name name'} :
  (env ⊢ e₁↓ → env' ⊢ e₁'↓) →
  (env' ⊢ e₁'↓ → env ⊢ e₁↓) →
  (∀ a a', env ⊢ e₁ ↦ a → env' ⊢ e₁' ↦ a' → e₂ ≈⟨a ∷ env, a' ∷ env'⟩ e₂') →
  Expr.save name e₁ e₂ ≈⟨env, env'⟩ Expr.save name' e₁' e₂' := by
  unfold Expr.Equiv.Param
  aesop (add unsafe Expr.Approx.Param.cong_save)

lemma Expr.Equiv.Param.cong_branch {constr names₁ names₂ e₁ e₂ e₁' e₂' a a' env env'} :
  a ≈ᵥ a' →
  (∀ args args', a = Value.constr_app constr args → a' = Value.constr_app constr args' →
    e₁ ≈⟨args.map Object.value ++ env, args'.map Object.value ++ env'⟩ e₁') →
  e₂ ≈⟨a ∷ env, a' ∷ env'⟩ e₂' →
  Expr.branch constr names₁ e₁ e₂ ≈⟨a ∷ env, a' ∷ env'⟩ Expr.branch constr names₂ e₁' e₂' := by
  unfold Expr.Equiv.Param Value.Equiv
  aesop (add unsafe Expr.Approx.Param.cong_branch)

lemma Expr.Equiv.Param.cong_recur {e e' env env' name name'} :
  e ≈⟨Object.delayed env (Expr.recur name e) :: env, Object.delayed env' (Expr.recur name' e') :: env'⟩ e' →
  Expr.recur name e ≈⟨env, env'⟩ Expr.recur name' e' := by
  unfold Expr.Equiv.Param
  aesop (add unsafe Expr.Approx.Param.cong_recur)

lemma Expr.Equiv.Param.cong_fail {env env'} :
  Expr.fail ≈⟨env, env'⟩ Expr.fail := by
  unfold Expr.Equiv.Param
  aesop (add unsafe Expr.Approx.Param.cong_fail)

end Juvix.Core.Main
