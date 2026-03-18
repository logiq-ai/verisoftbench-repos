
import Juvix.Core.Main.Semantics.Approx
import Juvix.Core.Main.Semantics.Approx.Contextual

namespace Juvix.Core.Main

def Context.Indexed.Preserved (k : Nat) : Prop :=
  ∀ n m,
    n + m < k →
    ∀ e₁ e₂,
      e₁ ≲'(n + m) e₂ → ∀ (C : Context) env₁ env₂ v₁,
      env₁ ≲ₑ'(n + m) env₂ →
      env₁ ⊢ C.subst e₁ ↦(n) v₁ →
      ∃ v₂, env₂ ⊢ C.subst e₂ ↦ v₂ ∧ v₁ ≲ᵥ(m) v₂

lemma Expr.Approx.Context.Indexed.preserved_step (k : Nat) :
  Context.Indexed.Preserved k → Context.Indexed.Preserved (k + 1) := by
  intro hstep n m hk e₁ e₂ happrox C env₁ env₂ v₁ henv heval
  induction C generalizing n m v₁ env₁ env₂ <;> simp_all
  case hole =>
    simp [Expr.Approx.Indexed'] at happrox
    obtain ⟨v₂, _⟩ := happrox n m v₁ (by linarith) env₁ env₂ henv heval
    exists v₂
  case app_left C arg ih =>
    cases heval
    case app n₁ n₂ env' body a hn heval₁ h_arg h_body =>
      have hexpr' : e₁ ≲'(n₁ + (n₂ + m + 1)) e₂ := Expr.Approx.Indexed'.anti_monotone happrox (by linarith)
      have henv' : env₁ ≲ₑ'(n₁ + (n₂ + m + 1)) env₂ := Env.Approx.Indexed'.anti_monotone henv (by linarith)
      obtain ⟨v₂', heval₂', happrox₂'⟩ := ih n₁ (n₂ + m + 1) (by linarith) hexpr' env₁ env₂ (Value.closure env' body) henv' heval₁
      invert happrox₂'
      case closure env₂' body₂ ch₂ =>
        have henv' : env₁ ≲ₑ'((n₂ + m) + (n₁ + 1)) env₂ := Env.Approx.Indexed'.anti_monotone henv (by linarith)
        obtain ⟨a', h_arg', happrox_arg'⟩ := Value.Approx.Indexed.preserved (n₂ + m) (n₁ + 1)  env₁ env₂ arg a henv' h_arg
        obtain ⟨v₂, heval₂, happrox₂⟩ := ch₂ n₂ m (by linarith) a a' v₁ happrox_arg' h_body
        exists v₂
        simp_all only [and_true]
        apply Juvix.Core.Main.Eval.app
        · exact heval₂'
        · exact h_arg'
        · simp_all only
  case app_right f C ih =>
    cases heval
    case app n₁ n₂ env' body v₁' hn h_f heval₁ h_body =>
      have henv' : env₁ ≲ₑ'(n₁ + 1 + (n₂ + m)) env₂ := Env.Approx.Indexed'.anti_monotone henv (by linarith)
      have hexpr' : e₁ ≲'(n₁ + 1 + (n₂ + m)) e₂ := Expr.Approx.Indexed'.anti_monotone happrox (by linarith)
      obtain ⟨v₂', heval₂', happrox₂'⟩ := ih (n₁ + 1) (n₂ + m) (by linarith) hexpr' env₁ env₂ v₁' henv' heval₁
      have henv'' : env₁ ≲ₑ'(n₂ + m + 1 + n₁) env₂ := Env.Approx.Indexed'.anti_monotone henv (by linarith)
      obtain ⟨c', h_f', happrox_f'⟩ := Value.Approx.Indexed.preserved (n₂ + m + 1) n₁ env₁ env₂ f (Value.closure env' body) henv'' h_f
      invert happrox_f'
      case closure env₂' body₂ ch₂ =>
        have henv : v₁' ∷ env₂' ≲ₑ'(m + n₂) v₂' ∷ env₂' := by
          have : m + n₂ = n₂ + m := by linarith
          rw [this]
          apply Env.Approx.Indexed'.cons
          · constructor; assumption
          · rfl
        obtain ⟨v₂, heval₂, happrox₂⟩ := ch₂ n₂ m (by linarith) v₁' v₂' v₁ happrox₂' h_body
        exists v₂
        simp_all only [and_true]
        apply Juvix.Core.Main.Eval.app
        · exact h_f'
        · exact heval₂'
        · simp_all only
  case constr_app_left C arg ih =>
    cases heval
    case constr_app n' cname args₁ a hn' heval₁ h_arg =>
      obtain ⟨v₂', heval₂', happrox₂'⟩ := ih n m (by linarith) happrox env₁ env₂ (Value.constr_app cname args₁) henv heval₁
      invert happrox₂'
      case constr_app args₂ ch₂ =>
        have henv' : env₁ ≲ₑ'(m + n') env₂ := Env.Approx.Indexed'.anti_monotone henv (by linarith)
        obtain ⟨a', h_arg', happrox_arg'⟩ := Value.Approx.Indexed.preserved m n' env₁ env₂ arg a henv' h_arg
        exists (Value.constr_app cname (a' :: args₂))
        constructor
        · apply Juvix.Core.Main.Eval.constr_app
          · exact heval₂'
          · exact h_arg'
        · apply Juvix.Core.Main.Value.Approx.Indexed.constr_app
          intro k' hk'
          simp_all only [List.forall₂_cons, and_true]
          apply Value.Approx.Indexed.anti_monotone happrox_arg'
          linarith
  case constr_app_right ctr C ih =>
    cases heval
    case constr_app n' cname args a hn' heval ha =>
      have henv' : env₁ ≲ₑ'(n' + m) env₂ := Env.Approx.Indexed'.anti_monotone henv (by linarith)
      have hexpr' : e₁ ≲'(n' + m) e₂ := Expr.Approx.Indexed'.anti_monotone happrox (by linarith)
      obtain ⟨a', heval', happrox'⟩ := ih n' m (by linarith) hexpr' env₁ env₂ a henv' ha
      have henv'' : env₁ ≲ₑ'(m + n) env₂ := Env.Approx.Indexed'.anti_monotone henv (by linarith)
      obtain ⟨ctr', h_ctr', happrox_ctr'⟩ := Value.Approx.Indexed.preserved m n env₁ env₂ ctr (Value.constr_app cname args) henv'' heval
      invert happrox_ctr'
      case constr_app args' hargs' =>
        exists (Value.constr_app cname (a' :: args'))
        constructor
        · apply Juvix.Core.Main.Eval.constr_app
          · exact h_ctr'
          · exact heval'
        · apply Juvix.Core.Main.Value.Approx.Indexed.constr_app
          intro k hk
          simp_all only [List.forall₂_cons, List.forall₂_same, and_true]
          apply Juvix.Core.Main.Value.Approx.Indexed.anti_monotone
          · exact happrox'
          · linarith
  case binop_left op C e ih =>
    cases heval
    case binop i₁ i₂ heval₁ heval₂ =>
      obtain ⟨v₂, heval₂', happrox₂'⟩ := ih n m hk happrox env₁ env₂ (Value.const (Constant.int i₁)) henv heval₁
      invert happrox₂'
      have henv' : env₁ ≲ₑ'(m + n) env₂ := Env.Approx.Indexed'.anti_monotone henv (by linarith)
      obtain ⟨c', h_c', happrox_c'⟩ := Value.Approx.Indexed.preserved m n env₁ env₂ e (Value.const (Constant.int i₂)) henv' heval₂
      invert happrox_c'
      exists (Value.const (Constant.int (eval_binop_int op i₁ i₂)))
      constructor
      · apply Juvix.Core.Main.Eval.binop
        · exact heval₂'
        · exact h_c'
      · simp_all only [Value.Approx.Indexed.const]
  case binop_right op e C ih =>
    cases heval
    case binop i₁ i₂ heval₁ heval₂ =>
      obtain ⟨v₂, heval₂', happrox₂'⟩ := ih n m hk happrox env₁ env₂ (Value.const (Constant.int i₂)) henv heval₂
      invert happrox₂'
      have henv' : env₁ ≲ₑ'(m + n) env₂ := Env.Approx.Indexed'.anti_monotone henv (by linarith)
      obtain ⟨c', h_c', happrox_c'⟩ := Value.Approx.Indexed.preserved m n env₁ env₂ e (Value.const (Constant.int i₁)) henv' heval₁
      invert happrox_c'
      exists (Value.const (Constant.int (eval_binop_int op i₁ i₂)))
      constructor
      · apply Juvix.Core.Main.Eval.binop
        · exact h_c'
        · exact heval₂'
      · simp_all only [Value.Approx.Indexed.const]
  case lambda C ih =>
    cases heval
    case lambda =>
      exists (Value.closure env₂ (C.subst e₂))
      constructor
      · apply Juvix.Core.Main.Eval.lambda
      · apply Value.Approx.Indexed.closure
        intro n₁ n₂ hm a₁ a₂ v₁ ha heval
        have henv : a₁ ∷ env₁ ≲ₑ'(n₁ + n₂) a₂ ∷ env₂ := by
          apply Env.Approx.Indexed'.cons
          · constructor; assumption
          · apply Env.Approx.Indexed'.anti_monotone henv (by linarith)
        have hexpr : e₁ ≲'(n₁ + n₂) e₂ := Expr.Approx.Indexed'.anti_monotone happrox (by linarith)
        obtain ⟨v₂, heval₂, happrox₂⟩ := hstep n₁ n₂ (by linarith) e₁ e₂ hexpr C (a₁ ∷ env₁) (a₂ ∷ env₂) v₁ henv heval
        exists v₂
  case save_left C e ih =>
    cases heval
    case save n₁ n₂ v₁' hn heval₁ heval₂ =>
      have henv' : env₁ ≲ₑ'(n₁ + (n₂ + m)) env₂ := Env.Approx.Indexed'.anti_monotone henv (by linarith)
      have hexpr' : e₁ ≲'(n₁ + (n₂ + m)) e₂ := Expr.Approx.Indexed'.anti_monotone happrox (by linarith)
      obtain ⟨v₂', heval₂', happrox₂'⟩ := ih n₁ (n₂ + m) (by linarith) hexpr' env₁ env₂ v₁' henv' heval₁
      have henv : v₁' ∷ env₁ ≲ₑ'(m + n₂) v₂' ∷ env₂ := by
        apply Env.Approx.Indexed'.cons
        · constructor
          have : m + n₂ = n₂ + m := by linarith
          rw [this]
          assumption
        · apply Env.Approx.Indexed'.anti_monotone henv (by linarith)
      obtain ⟨v₂, heval₂, happrox₂⟩ := Value.Approx.Indexed.preserved m n₂ (v₁' ∷ env₁) (v₂' ∷ env₂) e v₁ henv heval₂
      exists v₂
      constructor
      · apply Juvix.Core.Main.Eval.save
        · exact heval₂'
        · exact heval₂
      · simp_all only
  case save_right e C ih =>
    cases heval
    case save n₁ n₂ v' hn heval₁ heval₂ =>
      have henv'' : env₁ ≲ₑ'(m + n₂ + n₁) env₂ := Env.Approx.Indexed'.anti_monotone henv (by linarith)
      obtain ⟨v'', heval'', happrox''⟩ := Value.Approx.Indexed.preserved (m + n₂) n₁ env₁ env₂ e v' henv'' heval₁
      have henv' : v' ∷ env₁ ≲ₑ'(n₂ + m) v'' ∷ env₂ := by
        apply Env.Approx.Indexed'.cons
        · constructor
          apply Value.Approx.Indexed.anti_monotone happrox''
          linarith
        · apply Env.Approx.Indexed'.anti_monotone henv (by linarith)
      have hexpr' : e₁ ≲'(n₂ + m) e₂ := Expr.Approx.Indexed'.anti_monotone happrox (by linarith)
      obtain ⟨v₂, heval₂', happrox₂'⟩ := ih n₂ m (by linarith) hexpr' (v' ∷ env₁) (v'' ∷ env₂) v₁ henv' heval₂
      exists v₂
      constructor
      · apply Juvix.Core.Main.Eval.save
        · exact heval''
        · exact heval₂'
      · simp_all only
  case branch_left cname C e ih =>
    cases heval
    case branch_matches n' env₁' args hn heval =>
      cases henv
      case cons o env₂' happrox_o henv' =>
        cases happrox_o
        case value v' happrox_v' =>
          invert happrox_v'
          case constr_app args' hargs' =>
            have hexpr' : e₁ ≲'(n' + m) e₂ := Expr.Approx.Indexed'.anti_monotone happrox (by linarith)
            have henv'' : args.map Object.value ++ env₁' ≲ₑ'(n' + m) args'.map Object.value ++ env₂' := by
              apply Env.Approx.Indexed'.concat
              · apply Env.Approx.Indexed'.from_value
                apply hargs'
                linarith
              · apply Env.Approx.Indexed'.anti_monotone henv' (by linarith)
            obtain ⟨v₂, heval₂, happrox₂⟩ := ih n' m (by linarith) hexpr' (args.map Object.value ++ env₁') (args'.map Object.value ++ env₂') v₁ henv'' heval
            exists v₂
            constructor
            · apply Juvix.Core.Main.Eval.branch_matches
              · exact heval₂
            · simp_all only
    case branch_fails env₁' cname' args neq heval =>
      cases henv
      case cons o env₂' happrox_o henv' =>
        cases happrox_o
        case value v' happrox_v' =>
          invert happrox_v'
          case constr_app args' hargs' =>
            have henv'' : env₁' ≲ₑ'(m + n) env₂' := Env.Approx.Indexed'.anti_monotone henv' (by linarith)
            have henv''' : Value.constr_app cname' args ∷ env₁' ≲ₑ'(m + n) Value.constr_app cname' args' ∷ env₂' := by
              apply Env.Approx.Indexed'.cons
              · constructor
                apply Value.Approx.Indexed.constr_app
                have : m + n = n + m := by linarith
                rw [this]
                assumption
              · apply Env.Approx.Indexed'.anti_monotone henv'' (by linarith)
            obtain ⟨v₁', heval₁', happrox₁'⟩ := Value.Approx.Indexed.preserved m n (Value.constr_app cname' args ∷ env₁') (Value.constr_app cname' args' ∷ env₂') e v₁ henv''' heval
            exists v₁'
            constructor
            · apply Juvix.Core.Main.Eval.branch_fails
              · assumption
              · assumption
            · assumption
  case branch_right cname e C ih =>
    cases heval
    case branch_matches n' env₁' args hn heval =>
      cases henv
      case cons o env₂' happrox_o henv' =>
        cases happrox_o
        case value v' happrox_v' =>
          invert happrox_v'
          case constr_app args' hargs' =>
            have henv'' : args.map Object.value ++ env₁' ≲ₑ'(m + n') args'.map Object.value ++ env₂' := by
              apply Env.Approx.Indexed'.concat
              · apply Env.Approx.Indexed'.from_value
                apply hargs'
                linarith
              · apply Env.Approx.Indexed'.anti_monotone henv' (by linarith)
            obtain ⟨v₁', heval₁', happrox₁'⟩ := Value.Approx.Indexed.preserved m n' (args.map Object.value ++ env₁') (args'.map Object.value ++ env₂') e v₁ henv'' heval
            exists v₁'
            constructor
            · apply Juvix.Core.Main.Eval.branch_matches
              · assumption
            · assumption
    case branch_fails env₁' cname' args neq heval =>
      cases henv
      case cons o env₂' happrox_o henv' =>
        cases happrox_o
        case value v' happrox_v' =>
          invert happrox_v'
          case constr_app args' hargs' =>
            have hexpr' : e₁ ≲'(n + m) e₂ := Expr.Approx.Indexed'.anti_monotone happrox (by linarith)
            have henv'' : Value.constr_app cname' args ∷ env₁' ≲ₑ'(n + m) Value.constr_app cname' args' ∷ env₂' := by
              apply Env.Approx.Indexed'.cons
              · constructor
                apply Value.Approx.Indexed.constr_app
                assumption
              · apply Env.Approx.Indexed'.anti_monotone henv' (by linarith)
            obtain ⟨v₂, heval₂, happrox₂⟩ := ih n m hk hexpr' (Value.constr_app cname' args ∷ env₁') (Value.constr_app cname' args' ∷ env₂') v₁ henv'' heval
            exists v₂
            constructor
            · apply Juvix.Core.Main.Eval.branch_fails
              · assumption
              · assumption
            · simp_all only
  case recur name C ih =>
    cases heval
    case recur n' hn heval =>
      have hobj : Object.delayed env₁ (Expr.recur name (C.subst e₁)) ≲ₒ'(n' + m) Object.delayed env₂ (Expr.recur name (C.subst e₂)) := by
        apply Object.Approx.Indexed'.delayed
        intro n₁ n₂ v₁' hn' heval'
        have C_eq : ∀ e, Expr.recur name (C.subst e) = (Context.recur name C).subst e := by intro; rfl
        rw [C_eq]
        apply hstep n₁ n₂ (by linarith) e₁ e₂
        · apply Expr.Approx.Indexed'.anti_monotone happrox
          linarith
        · apply Env.Approx.Indexed'.anti_monotone henv
          linarith
        · assumption
      let env₁' := Object.delayed env₁ (Expr.recur name (C.subst e₁)) :: env₁
      let env₂' := Object.delayed env₂ (Expr.recur name (C.subst e₂)) :: env₂
      have henv' : env₁' ≲ₑ'(n' + m) env₂' := by
        apply Env.Approx.Indexed'.cons
        · apply hobj
        · apply Env.Approx.Indexed'.anti_monotone henv
          linarith
      have hexpr' : e₁ ≲'(n' + m) e₂ := Expr.Approx.Indexed'.anti_monotone happrox (by linarith)
      obtain ⟨v₂, heval₂, happrox₂⟩ := ih n' m (by linarith) hexpr' env₁' env₂' v₁ henv' heval
      exists v₂
      constructor
      · apply Juvix.Core.Main.Eval.recur
        · assumption
      · simp_all only

lemma Expr.Approx.Context.Indexed.preserved (k : Nat) :
  Context.Indexed.Preserved k := by
  induction k with
  | zero =>
    intro n m hk e₁ e₂ happrox C env₁ env₂ v₁ henv heval
    have : n + m < 0 := by linarith
    exfalso
    linarith
  | succ k ih =>
    apply Expr.Approx.Context.Indexed.preserved_step k ih

lemma Expr.Approx.Context.preserved (e₁ e₂ : Expr) :
  e₁ ≲ e₂ →
  ∀ (C : Context) env₁ env₂ v₁,
  env₁ ≲ₑ env₂ → env₁ ⊢ C.subst e₁ ↦ v₁ →
  ∃ v₂, env₂ ⊢ C.subst e₂ ↦ v₂ ∧ v₁ ≲ᵥ v₂ := by
  intro happrox C env₁ env₂ v₁ henv heval
  obtain ⟨n, heval'⟩ := Eval.toIndexed heval
  have happrox' : e₁ ≲'(n + 0) e₂ := by apply Expr.Approx.toIndexed happrox
  have henv' : env₁ ≲ₑ'(n + 0) env₂ := by apply Env.Approx.toIndexed henv
  obtain ⟨v₂, heval₂, happrox₂⟩ := Expr.Approx.Context.Indexed.preserved (n + 1) n 0 (by linarith) e₁ e₂ happrox' C env₁ env₂ v₁ henv' heval'
  have : ∀ m, v₁ ≲ᵥ(m) v₂ := by
    intro m
    have happrox_m : e₁ ≲'(n + m) e₂ := by apply Expr.Approx.toIndexed happrox
    have henv_m : env₁ ≲ₑ'(n + m) env₂ := by apply Env.Approx.toIndexed henv
    obtain ⟨v₂', heval₂', happrox₂'⟩ := Expr.Approx.Context.Indexed.preserved (n + m + 1) n m (by linarith) e₁ e₂ happrox_m C env₁ env₂ v₁ henv_m heval'
    have : v₂ = v₂' := Eval.deterministic heval₂ heval₂'
    rw [this]
    assumption
  exists v₂

theorem Expr.Approx.soundness (e₁ e₂ : Expr) : e₁ ≲ e₂ → e₁ ≲ᶜ e₂ := by
  intro h C env ⟨v₁, heval₁⟩
  simp [Eval.Defined]
  obtain ⟨v₂, heval₂, happrox⟩ := Expr.Approx.Context.preserved e₁ e₂ h C env env v₁ (by rfl) heval₁
  exists v₂

end Juvix.Core.Main
