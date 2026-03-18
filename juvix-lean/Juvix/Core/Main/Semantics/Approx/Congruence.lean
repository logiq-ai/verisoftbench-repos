
import Juvix.Core.Main.Semantics.Approx.Soundness

namespace Juvix.Core.Main

lemma Expr.Approx.congruence {e₁ e₂} (C : Context) : e₁ ≲ e₂ → C.subst e₁ ≲ C.subst e₂ := by
  intro h
  simp only [Expr.Approx, Expr.Approx.Param]
  intro env₁ env₂ happrox v₁ heval
  apply Expr.Approx.Context.preserved <;> assumption

lemma Expr.Approx.cong_app₁ {e₁ e₂ e₁'} : e₁ ≲ e₁' → Expr.app e₁ e₂ ≲ Expr.app e₁' e₂ := by
  intro h
  apply Expr.Approx.congruence (Context.app_left Context.hole e₂)
  assumption

lemma Expr.Approx.cong_app₂ {e₁ e₂ e₂'} : e₂ ≲ e₂' → Expr.app e₁ e₂ ≲ Expr.app e₁ e₂' := by
  intro h
  apply Expr.Approx.congruence (Context.app_right e₁ Context.hole)
  assumption

lemma Expr.Approx.cong_app {e₁ e₂ e₁' e₂'} : e₁ ≲ e₁' → e₂ ≲ e₂' → Expr.app e₁ e₂ ≲ Expr.app e₁' e₂' := by
  intros
  apply Juvix.Core.Main.Expr.Approx.trans
  apply Juvix.Core.Main.Expr.Approx.cong_app₁
  · assumption
  · apply Juvix.Core.Main.Expr.Approx.cong_app₂
    assumption

lemma Expr.Approx.cong_constr_app₁ {e₁ e₂ e₁'} : e₁ ≲ e₁' → Expr.constr_app e₁ e₂ ≲ Expr.constr_app e₁' e₂ := by
  intros
  apply Expr.Approx.congruence (Context.constr_app_left Context.hole e₂)
  assumption

lemma Expr.Approx.cong_constr_app₂ {e₁ e₂ e₂'} : e₂ ≲ e₂' → Expr.constr_app e₁ e₂ ≲ Expr.constr_app e₁ e₂' := by
  intros
  apply Expr.Approx.congruence (Context.constr_app_right e₁ Context.hole)
  assumption

lemma Expr.Approx.cong_constr_app {e₁ e₂ e₁' e₂'} : e₁ ≲ e₁' → e₂ ≲ e₂' → Expr.constr_app e₁ e₂ ≲ Expr.constr_app e₁' e₂' := by
  intros
  apply Juvix.Core.Main.Expr.Approx.trans
  apply Juvix.Core.Main.Expr.Approx.cong_constr_app₁
  · assumption
  · apply Juvix.Core.Main.Expr.Approx.cong_constr_app₂
    assumption

lemma Expr.Approx.cong_binop₁ {op e₁ e₂ e₁'} : e₁ ≲ e₁' → Expr.binop op e₁ e₂ ≲ Expr.binop op e₁' e₂ := by
  intros
  apply Juvix.Core.Main.Expr.Approx.congruence (Context.binop_left op Context.hole e₂)
  assumption

lemma Expr.Approx.cong_binop₂ {op e₁ e₂ e₂'} : e₂ ≲ e₂' → Expr.binop op e₁ e₂ ≲ Expr.binop op e₁ e₂' := by
  intros
  apply Juvix.Core.Main.Expr.Approx.congruence (Context.binop_right op e₁ Context.hole)
  assumption

lemma Expr.Approx.cong_binop {op e₁ e₂ e₁' e₂'} : e₁ ≲ e₁' → e₂ ≲ e₂' → Expr.binop op e₁ e₂ ≲ Expr.binop op e₁' e₂' := by
  intros
  apply Juvix.Core.Main.Expr.Approx.trans
  apply Juvix.Core.Main.Expr.Approx.cong_binop₁
  · assumption
  · apply Juvix.Core.Main.Expr.Approx.cong_binop₂
    assumption

lemma Expr.Approx.cong_lambda {name e e'} : e ≲ e' → Expr.lambda name e ≲ Expr.lambda name e' := by
  intros
  apply Juvix.Core.Main.Expr.Approx.congruence (Context.lambda name Context.hole)
  assumption

lemma Expr.Approx.cong_save₁ {name e₁ e₂ e₁'} : e₁ ≲ e₁' → Expr.save name e₁ e₂ ≲ Expr.save name e₁' e₂ := by
  intros
  apply Juvix.Core.Main.Expr.Approx.congruence (Context.save_left name Context.hole e₂)
  assumption

lemma Expr.Approx.cong_save₂ {name e₁ e₂ e₂'} : e₂ ≲ e₂' → Expr.save name e₁ e₂ ≲ Expr.save name e₁ e₂' := by
  intros
  apply Juvix.Core.Main.Expr.Approx.congruence (Context.save_right name e₁ Context.hole)
  assumption

lemma Expr.Approx.cong_save {name e₁ e₂ e₁' e₂'} : e₁ ≲ e₁' → e₂ ≲ e₂' → Expr.save name e₁ e₂ ≲ Expr.save name e₁' e₂' := by
  intros
  apply Juvix.Core.Main.Expr.Approx.trans
  apply Juvix.Core.Main.Expr.Approx.cong_save₁
  · assumption
  · apply Juvix.Core.Main.Expr.Approx.cong_save₂
    assumption

lemma Expr.Approx.cong_branch₁ {constr names e e' next} : e ≲ e' → Expr.branch constr names e next ≲ Expr.branch constr names e' next := by
  intros
  apply Juvix.Core.Main.Expr.Approx.congruence (Context.branch_left constr names Context.hole next)
  assumption

lemma Expr.Approx.cong_branch₂ {constr names e next next'} : next ≲ next' → Expr.branch constr names e next ≲ Expr.branch constr names e next' := by
  intros
  apply Juvix.Core.Main.Expr.Approx.congruence (Context.branch_right constr names e Context.hole)
  assumption

lemma Expr.Approx.cong_branch {constr names e e' next next'} : e ≲ e' → next ≲ next' → Expr.branch constr names e next ≲ Expr.branch constr names e' next' := by
  intros
  apply Juvix.Core.Main.Expr.Approx.trans
  apply Juvix.Core.Main.Expr.Approx.cong_branch₁
  · assumption
  · apply Juvix.Core.Main.Expr.Approx.cong_branch₂
    assumption

lemma Expr.Approx.cong_recur {name e e'} : e ≲ e' → Expr.recur name e ≲ Expr.recur name e' := by
  intros
  apply Juvix.Core.Main.Expr.Approx.congruence (Context.recur name Context.hole)
  assumption

lemma Expr.Approx.Param.cong_var {v v' x x' env env' name name'} :
  env[x]? = some (Object.value v) →
  env'[x']? = some (Object.value v') →
  v ≲ᵥ v' →
  Expr.var name x ≲⟨env, env'⟩ Expr.var name' x' := by
  intro h₁ h₂ h₃ v heval
  cases heval
  case var _ h =>
    rw [h₁] at h
    cases h
    exists v'
    constructor
    · constructor
      assumption
    · assumption
  case var_rec v₁ e₁ h h' =>
    rw [h₁] at h
    cases h

lemma Expr.Approx.Param.cong_unit {env env'} :
  Expr.unit ≲⟨env, env'⟩ Expr.unit := by
  intro v heval
  cases heval
  case unit =>
    exists Value.unit
    constructor
    · constructor
    · rfl

lemma Expr.Approx.Param.cong_const {c env env'} :
  Expr.const c ≲⟨env, env'⟩ Expr.const c := by
  intro v heval
  cases heval
  case const =>
    exists Value.const c
    constructor
    · constructor
    · rfl

lemma Expr.Approx.Param.cong_constr {cname env env'} :
  Expr.constr cname ≲⟨env, env'⟩ Expr.constr cname := by
  intro v heval
  cases heval
  case constr =>
    exists Value.constr_app cname []
    constructor
    · constructor
    · rfl

lemma Expr.Approx.Param.cong_app {e₁ e₂ e₁' e₂' env env'} :
  e₁ ≲⟨env, env'⟩ e₁' →
  e₂ ≲⟨env, env'⟩ e₂' →
  Expr.app e₁ e₂ ≲⟨env, env'⟩ Expr.app e₁' e₂' := by
  intro h₁ h₂ v heval
  cases heval
  case app cenv body val heval₁ heval₂ heval₃ =>
    obtain ⟨v₁', heval₁', happrox₁'⟩ := h₁ (Value.closure cenv body) heval₁
    obtain ⟨val', heval₂', happrox₂'⟩ := h₂ val heval₂
    invert happrox₁'
    case closure cenv' body' h =>
      obtain ⟨v', heval', happrox'⟩ := h val val' happrox₂' v heval₃
      exists v'
      constructor
      · constructor <;> assumption
      · assumption

lemma Expr.Approx.Param.cong_constr_app {e₁ e₂ e₁' e₂' env env'} :
  e₁ ≲⟨env, env'⟩ e₁' →
  e₂ ≲⟨env, env'⟩ e₂' →
  Expr.constr_app e₁ e₂ ≲⟨env, env'⟩ Expr.constr_app e₁' e₂' := by
  intro h₁ h₂ v heval
  cases heval
  case constr_app cname args val heval₁ heval₂ =>
    obtain ⟨v₁', heval₁', happrox₁'⟩ := h₁ (Value.constr_app cname args) heval₁
    obtain ⟨val', heval₂', happrox₂'⟩ := h₂ val heval₂
    invert happrox₁'
    case constr_app args' hargs =>
      exists (Value.constr_app cname (val' :: args'))
      constructor
      · constructor <;> assumption
      · apply Value.Approx.constr_app
        constructor <;> assumption

lemma Expr.Approx.Param.cong_binop {op e₁ e₂ e₁' e₂' env env'} :
  e₁ ≲⟨env, env'⟩ e₁' →
  e₂ ≲⟨env, env'⟩ e₂' →
  Expr.binop op e₁ e₂ ≲⟨env, env'⟩ Expr.binop op e₁' e₂' := by
  intro h₁ h₂ v heval
  cases heval
  case binop val₁ val₂ heval₁ heval₂ =>
    obtain ⟨val₁', heval₁', happrox⟩ := h₁ (Value.const (Constant.int val₁)) heval₁
    obtain ⟨val₂', heval₂', happrox'⟩ := h₂ (Value.const (Constant.int val₂)) heval₂
    invert happrox
    invert happrox'
    exists (Value.const (Constant.int (eval_binop_int op val₁ val₂)))
    constructor
    · constructor <;> assumption
    · rfl

lemma Expr.Approx.Param.cong_lambda {e e' env₁ env₂ name₁ name₂} :
  (∀ a₁ a₂, a₁ ≲ᵥ a₂ → e ≲⟨a₁ ∷ env₁, a₂ ∷ env₂⟩ e') →
  Expr.lambda name₁ e ≲⟨env₁, env₂⟩ Expr.lambda name₂ e' := by
  intro h v heval
  cases heval
  case lambda =>
    exists Value.closure env₂ e'
    constructor
    · constructor
    · apply Value.Approx.closure
      intro a₁ a₂ happrox
      apply h
      assumption

lemma Expr.Approx.Param.cong_save {e₁ e₂ e₁' e₂' env env' name name'} :
  (env ⊢ e₁↓ → env' ⊢ e₁'↓) →
  (∀ a a', env ⊢ e₁ ↦ a → env' ⊢ e₁' ↦ a' → e₂ ≲⟨a ∷ env, a' ∷ env'⟩ e₂') →
  Expr.save name e₁ e₂ ≲⟨env, env'⟩ Expr.save name' e₁' e₂' := by
  intro h₁ h₂ v heval
  cases heval
  case save a heval₁ heval₂ =>
    have : env ⊢ e₁↓ := by
      constructor
      assumption
    obtain ⟨a', heval₁'⟩ := h₁ this
    obtain ⟨v', heval₂', happrox₂'⟩ := h₂ a a' heval₁ heval₁' v heval₂
    exists v'
    constructor
    · constructor <;> assumption
    · assumption

lemma Expr.Approx.Param.cong_branch {constr names names' e e' next next' a a' env env'} :
  a ≲ᵥ a' →
  (∀ args args', a = Value.constr_app constr args → a' = Value.constr_app constr args' →
    e ≲⟨args.map Object.value ++ env, args'.map Object.value ++ env'⟩ e') →
  next ≲⟨a ∷ env, a' ∷ env'⟩ next' →
  Expr.branch constr names e next ≲⟨a ∷ env, a' ∷ env'⟩ Expr.branch constr names' e' next' := by
  intro ha h₁ h₂ v heval
  cases heval
  case branch_matches args heval =>
    invert ha
    case constr_app args' hargs =>
      obtain ⟨v', heval₁', happrox₁'⟩ := h₁ args args' (by rfl) (by rfl) v heval
      exists v'
      constructor
      · constructor; assumption
      · assumption
  case branch_fails constr' args hconstr heval =>
    obtain ⟨v', heval', happrox'⟩ := h₂ v heval
    exists v'
    constructor
    · invert ha
      case constr_app args' hargs =>
        constructor <;> assumption
    · assumption

lemma Expr.Approx.Param.cong_recur {e e' env env' name name'} :
  e ≲⟨Object.delayed env (Expr.recur name e) :: env, Object.delayed env' (Expr.recur name' e') :: env'⟩ e' →
  Expr.recur name e ≲⟨env, env'⟩ Expr.recur name' e' := by
  intro h v heval
  cases heval
  case recur heval =>
    obtain ⟨val', heval', happrox'⟩ := h v heval
    exists val'
    constructor
    · constructor; assumption
    · assumption

lemma Expr.Approx.Param.cong_fail {e env env'} :
  Expr.fail ≲⟨env, env'⟩ e := by
  intro v heval
  cases heval

end Juvix.Core.Main
