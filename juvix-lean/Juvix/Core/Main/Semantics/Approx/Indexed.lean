
import Juvix.Core.Main.Semantics.Eval
import Juvix.Core.Main.Semantics.Eval.Indexed
import Juvix.Utils
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Forall2
import Aesop

namespace Juvix.Core.Main

def Value.Approx.Indexed (n : Nat) (v₁ v₂ : Value) : Prop :=
  (v₁ = Value.unit ∧ v₂ = Value.unit) ∨
  (∃ c, v₁ = Value.const c ∧ v₂ = Value.const c) ∨
  (∃ ctr_name args_rev args_rev',
    v₁ = Value.constr_app ctr_name args_rev ∧
    v₂ = Value.constr_app ctr_name args_rev' ∧
    (∀ k < n, List.Forall₂ (Value.Approx.Indexed k) args_rev args_rev')) ∨
  (∃ env₁ body₁ env₂ body₂,
    v₁ = Value.closure env₁ body₁ ∧
    v₂ = Value.closure env₂ body₂ ∧
    (∀ n₁ n₂, n₁ + n₂ < n →
      ∀ a₁ a₂ r₁,
        Value.Approx.Indexed (n₁ + n₂) a₁ a₂ →
        a₁ ∷ env₁ ⊢ body₁ ↦(n₁) r₁ →
        ∃ r₂,
          a₂ ∷ env₂ ⊢ body₂ ↦ r₂ ∧
          Value.Approx.Indexed n₂ r₁ r₂))

notation:40 v:40 " ≲ᵥ(" n:40 ") " v':40 => Value.Approx.Indexed n v v'

notation:40 args₁:40 " ≲ₐ(" n:40 ") " args₂:40 => List.Forall₂ (Value.Approx.Indexed n) args₁ args₂

def Expr.Approx.Param.Indexed (n : Nat) (env₁ env₂ : Env) (e₁ e₂ : Expr) : Prop :=
  (∀ n₁ n₂ v₁, n₁ + n₂ ≤ n → env₁ ⊢ e₁ ↦(n₁) v₁ → ∃ v₂, env₂ ⊢ e₂ ↦ v₂ ∧ v₁ ≲ᵥ(n₂) v₂)

notation:40 e:40 " ≲(" n:40 ")⟨" env:40 ", " env':40 "⟩ " e':40 => Expr.Approx.Param.Indexed n env env' e e'

inductive Object.Approx.Indexed' (n : Nat) : Object → Object → Prop where
  | value {v₁ v₂} :
    v₁ ≲ᵥ(n) v₂ →
    Object.Approx.Indexed' n (Object.value v₁) (Object.value v₂)
  | delayed {env₁ env₂ e₁ e₂} :
    e₁ ≲(n)⟨env₁, env₂⟩ e₂ →
    Object.Approx.Indexed' n (Object.delayed env₁ e₁) (Object.delayed env₂ e₂)
  | delayed_eq {env₁ env₂ e} :
    List.Forall₂ (Object.Approx.Indexed' n) env₁ env₂ →
    Object.Approx.Indexed' n (Object.delayed env₁ e) (Object.delayed env₂ e)

def Env.Approx.Indexed' (n : Nat) : (env₁ env₂ : Env) → Prop :=
  List.Forall₂ (Object.Approx.Indexed' n)

notation:40 v:40 " ≲ₒ'(" n:40 ") " v':40 => Object.Approx.Indexed' n v v'

notation:40 env₁:40 " ≲ₑ'(" n:40 ") " env₂:40 => Env.Approx.Indexed' n env₁ env₂

def Expr.Approx.Indexed' (n : Nat) (e₁ e₂ : Expr) : Prop :=
  (∀ n₁ n₂ v₁, n₁ + n₂ ≤ n →
    ∀ env₁ env₂, env₁ ≲ₑ'(n₁ + n₂) env₂ → env₁ ⊢ e₁ ↦(n₁) v₁ → ∃ v₂, env₂ ⊢ e₂ ↦ v₂ ∧ v₁ ≲ᵥ(n₂) v₂)

notation:40 e:40 " ≲'(" n:40 ") " e':40 => Expr.Approx.Indexed' n e e'

macro "invert" h:term : tactic => `(tactic| (cases ($h).invert <;> try clear $h))

lemma Env.Approx.Indexed'.get {n i : Nat} {env env' o₁}
  (h₁ : env ≲ₑ'(n) env')
  (h₂ : env[i]? = some o₁) :
  ∃ o₂, env'[i]? = some o₂ ∧ o₁ ≲ₒ'(n) o₂ := by
  have h' := List.Forall₂.get h₁
  have : env.length = env'.length := by
    apply List.Forall₂.length_eq
    assumption
  have : i < env.length := by
    rw [@List.getElem?_eq_some_iff] at h₂
    obtain ⟨w, h⟩ := h₂
    subst h
    simp_all only [List.get_eq_getElem, forall_true_left]
  aesop

lemma Env.Approx.Indexed'.value {n i : Nat} {env env' v}
  (h₁ : env ≲ₑ'(n) env')
  (h₂ : env[i]? = some (Object.value v)) :
  ∃ v', env'[i]? = some (Object.value v') ∧ v ≲ᵥ(n) v' := by
  obtain ⟨o, h, happrox⟩ := Env.Approx.Indexed'.get h₁ h₂
  cases happrox
  case value v' hv' =>
    exists v'

lemma Env.Approx.Indexed'.delayed {n i : Nat} {env₁ env₂ env e}
  (h₁ : env₁ ≲ₑ'(n) env₂)
  (h₂ : env₁[i]? = some (Object.delayed env e)) :
  (∃ env' e', e ≲(n)⟨env, env'⟩ e' ∧ env₂[i]? = some (Object.delayed env' e')) ∨
  ∃ env', env ≲ₑ'(n) env' ∧ env₂[i]? = some (Object.delayed env' e) := by
  obtain ⟨o, h, happrox⟩ := Env.Approx.Indexed'.get h₁ h₂
  cases h₃ : o
  case value v =>
    rw [h₃] at happrox
    contradiction
  case delayed env' e' =>
    rw [h₃] at happrox
    cases happrox
    case delayed h =>
      left
      subst h₃
      exists env'
      exists e'
    case delayed_eq =>
      right
      subst h₃
      exists env'

lemma Env.Approx.Indexed'.from_value {n l₁ l₂} (h : l₁ ≲ₐ(n) l₂) :
  List.map Object.value l₁ ≲ₑ'(n) List.map Object.value l₂ := by
  induction h
  case nil =>
    exact List.Forall₂.nil
  case cons v₁ v₂ l₁' l₂' hv h₁ h₂ =>
    refine List.Forall₂.cons ?_ h₂
    constructor
    assumption

lemma Env.Approx.Indexed'.from_delayed {n env₁ env₂ l} (h : env₁ ≲ₑ'(n) env₂) :
  List.map (Object.delayed env₁) l ≲ₑ'(n) List.map (Object.delayed env₂) l := by
  induction l
  case nil =>
    exact List.Forall₂.nil
  case cons e l' h' =>
    simp
    apply List.Forall₂.cons
    · apply Object.Approx.Indexed'.delayed_eq
      assumption
    · assumption

lemma Env.Approx.Indexed'.concat {n env₁ env₂ env₁' env₂'}
  (h₁ : env₁ ≲ₑ'(n) env₁')
  (h₂ : env₂ ≲ₑ'(n) env₂') :
  env₁ ++ env₂ ≲ₑ'(n) env₁' ++ env₂' := by
  induction h₁
  case nil =>
    simp
    assumption
  case cons hd₁ hd₁' tl₁ tl₁' h₁ h₂ ih =>
    simp
    constructor
    · exact h₁
    · exact ih

lemma Env.Approx.Indexed'.cons {n o₁ o₂ env₁ env₂}
  (h₁ : o₁ ≲ₒ'(n) o₂)
  (h₂ : env₁ ≲ₑ'(n) env₂) :
  o₁ :: env₁ ≲ₑ'(n) o₂ :: env₂ := by
  constructor <;> assumption

@[aesop unsafe apply]
lemma Value.Approx.Indexed.unit {n} : Value.unit ≲ᵥ(n) Value.unit := by
  unfold Value.Approx.Indexed
  simp

@[aesop unsafe apply]
lemma Value.Approx.Indexed.const {n c} : Value.const c ≲ᵥ(n) Value.const c := by
  unfold Value.Approx.Indexed
  simp

@[aesop unsafe apply]
lemma Value.Approx.Indexed.constr_app {n ctr_name args_rev args_rev'} :
    (∀ k < n, args_rev ≲ₐ(k) args_rev') →
    Value.constr_app ctr_name args_rev ≲ᵥ(n) Value.constr_app ctr_name args_rev' := by
  intro h
  unfold Value.Approx.Indexed
  simp only [reduceCtorEq, and_self, exists_const, constr_app.injEq, Prod.forall, exists_and_left,
    false_and, or_false, false_or]
  exists ctr_name
  exists args_rev
  simp_all only [Prod.forall, and_self, true_and, exists_eq_left', implies_true]

@[aesop unsafe apply]
lemma Value.Approx.Indexed.closure {n env₁ body₁ env₂ body₂} :
    (∀ n₁ n₂, n₁ + n₂ < n →
      ∀ a₁ a₂ v₁,
        a₁ ≲ᵥ(n₁ + n₂) a₂ →
        a₁ ∷ env₁ ⊢ body₁ ↦(n₁) v₁ →
        ∃ v₂, a₂ ∷ env₂ ⊢ body₂ ↦ v₂ ∧ v₁ ≲ᵥ(n₂) v₂) →
    Value.closure env₁ body₁ ≲ᵥ(n) Value.closure env₂ body₂ := by
  intro h
  unfold Value.Approx.Indexed
  simp only [reduceCtorEq, and_self, exists_const, Prod.forall, false_and, closure.injEq,
    exists_and_left, false_or]
  exists env₁
  exists body₁
  simp only [and_self, true_and]
  exists env₂
  exists body₂

@[aesop safe cases]
inductive Value.Approx.Indexed.Inversion (n : Nat) : Value → Value → Prop where
  | unit : Value.Approx.Indexed.Inversion n Value.unit Value.unit
  | const {c} : Value.Approx.Indexed.Inversion n (Value.const c) (Value.const c)
  | constr_app {ctr_name args_rev args_rev'} :
    (∀ k < n, args_rev ≲ₐ(k) args_rev') →
    Value.Approx.Indexed.Inversion n (Value.constr_app ctr_name args_rev) (Value.constr_app ctr_name args_rev')
  | closure {env₁ body₁ env₂ body₂} :
    (∀ n₁ n₂, n₁ + n₂ < n →
      ∀ a₁ a₂ v₁,
        a₁ ≲ᵥ(n₁ + n₂) a₂ →
        a₁ ∷ env₁ ⊢ body₁ ↦(n₁) v₁ →
        ∃ v₂, a₂ ∷ env₂ ⊢ body₂ ↦ v₂ ∧ v₁ ≲ᵥ(n₂) v₂) →
    Value.Approx.Indexed.Inversion n (Value.closure env₁ body₁) (Value.closure env₂ body₂)

-- Use `invert h` to invert `h : v ≲(n) v'`.
@[aesop unsafe destruct]
lemma Value.Approx.Indexed.invert {n v v'} :
  v ≲ᵥ(n) v' →
  Value.Approx.Indexed.Inversion n v v' := by
  intro h
  unfold Value.Approx.Indexed at h
  rcases h with
    ⟨h₁, h₂⟩ |
    ⟨c, h₁, h₂⟩ |
    ⟨ctr_name, args_rev, args_rev', h₁, h₂, hargs⟩ |
    ⟨env₁, body₁, env₂, body₂, h₁, h₂, h⟩
  · subst h₁ h₂
    exact Value.Approx.Indexed.Inversion.unit
  · subst h₁ h₂
    exact Value.Approx.Indexed.Inversion.const
  · subst h₁ h₂
    exact Value.Approx.Indexed.Inversion.constr_app hargs
  · subst h₁ h₂
    exact Value.Approx.Indexed.Inversion.closure h

theorem Value.Approx.Indexed.anti_monotone {n n' : Nat} {v₁ v₂ : Value} (h : v₁ ≲ᵥ(n) v₂) (h' : n' ≤ n) : v₁ ≲ᵥ(n') v₂ := by
  invert h
  case unit =>
    exact Value.Approx.Indexed.unit
  case const =>
    exact Value.Approx.Indexed.const
  case constr_app ctr_name args_rev args_rev' hargs =>
    apply Value.Approx.Indexed.constr_app
    intro k hk
    exact hargs k (lt_of_lt_of_le hk h')
  case closure env₁ body₁ env₂ body₂ hcl =>
    apply Value.Approx.Indexed.closure
    intro n₁ n₂ hlt a₁ a₂ r₁ happrox heval
    exact hcl n₁ n₂ (lt_of_lt_of_le hlt h') a₁ a₂ r₁ happrox heval


lemma Expr.Approx.Param.Indexed.anti_monotone {n n' env₁ env₂ e₁ e₂}
  (h : e₁ ≲(n)⟨env₁, env₂⟩ e₂)
  (h' : n' ≤ n)
  : e₁ ≲(n')⟨env₁, env₂⟩ e₂ := by
  simp [Expr.Approx.Param.Indexed] at *
  intro n₁ n₂ v₁ hlt heval₁
  exact h n₁ n₂ v₁ (by linarith) heval₁

lemma Expr.Approx.Indexed'.anti_monotone {n n' e₁ e₂}
  (h : e₁ ≲'(n) e₂)
  (h' : n' ≤ n)
  : e₁ ≲'(n') e₂ := by
  simp [Expr.Approx.Indexed'] at *
  intro n₁ n₂ v₁ hlt heval₁
  exact h n₁ n₂ v₁ (by linarith) heval₁

mutual
  lemma Env.Approx.Indexed'.anti_monotone {n n' env₁ env₂}
    (h : env₁ ≲ₑ'(n) env₂)
    (h' : n' ≤ n)
    : env₁ ≲ₑ'(n') env₂ :=
    match h with
    | List.Forall₂.nil =>
      List.Forall₂.nil
    | List.Forall₂.cons h₁ h₂ =>
      List.Forall₂.cons (Object.Approx.Indexed'.anti_monotone h₁ h') (Env.Approx.Indexed'.anti_monotone h₂ h')

  lemma Object.Approx.Indexed'.anti_monotone {n n' o₁ o₂} (h : o₁ ≲ₒ'(n) o₂) (h' : n' ≤ n) : o₁ ≲ₒ'(n') o₂ :=
    match h with
    | @Object.Approx.Indexed'.value n v₁ v₂ happrox => by
      apply Object.Approx.Indexed'.value
      · apply Value.Approx.Indexed.anti_monotone
        · assumption
        · assumption
    | @Object.Approx.Indexed'.delayed n env₁ env₂ e₁ e₂ happrox => by
      apply Object.Approx.Indexed'.delayed
      apply Expr.Approx.Param.Indexed.anti_monotone
      · assumption
      · assumption
    | @Object.Approx.Indexed'.delayed_eq n env₁ env₂ e happrox =>
      Object.Approx.Indexed'.delayed_eq (Env.Approx.Indexed'.anti_monotone happrox h')
end

def Value.Approx.Indexed.Preservation (k : Nat) : Prop :=
  ∀ m n env env' e v,
    m + n < k →
    env ≲ₑ'(m + n) env' →
    env ⊢ e ↦(n) v →
    ∃ v', env' ⊢ e ↦ v' ∧ v ≲ᵥ(m) v'

lemma Value.Approx.Indexed.Preservation.anti_monotone {k k'} (h : Value.Approx.Indexed.Preservation k) (h' : k' ≤ k) : Value.Approx.Indexed.Preservation k' := by
  intro m n env env' e v h₀ h₁ h₂
  refine h m n env env' e v ?_ h₁ h₂
  linarith

lemma Value.Approx.Indexed.preserved_step {k} :
  (∀ k' < k, Preservation k') → Preservation k := by
  intro ihk
  intro m n env env' e v h₀ h₁ h₂
  induction h₂ generalizing m env'
  case var env i v h =>
    obtain ⟨v', hget, happrox⟩ := Env.Approx.Indexed'.value h₁ h
    exists v'
    constructor
    · apply Eval.var
      aesop
    · apply Value.Approx.Indexed.anti_monotone
      · assumption
      · linarith
  case var_rec n' env₁ name i env₁' e₁' v' hget heval ih =>
    have hget_or :
        (∃ env₂' e₂', e₁' ≲(m + n')⟨env₁', env₂'⟩ e₂' ∧
          env'[i]? = some (Object.delayed env₂' e₂')) ∨
        (∃ env₂', env₁' ≲ₑ'(m + n') env₂' ∧
          env'[i]? = some (Object.delayed env₂' e₁')) := by
      apply Env.Approx.Indexed'.delayed h₁; assumption
    cases hget_or
    case inl hget' =>
      obtain ⟨env₂', e₂', h₂, hget'⟩ := hget'
      simp [Expr.Approx.Param.Indexed] at h₂
      obtain ⟨v'', heval', happrox'⟩ := h₂ n' m v' (by linarith) heval
      exists v''
      constructor
      · apply Eval.var_rec
        · exact hget'
        · assumption
      · assumption
    case inr hget' =>
      obtain ⟨env₂, happrox, hget'⟩ := hget'
      obtain ⟨v'', heval', happrox'⟩ := ih m env₂ (by linarith) happrox
      exists v''
      constructor
      · apply Eval.var_rec
        · exact hget'
        · assumption
      · assumption
  case unit =>
    exists Value.unit
    constructor
    · apply Eval.unit
    · apply Value.Approx.Indexed.unit
  case const c =>
    exists Value.const c
    constructor
    · apply Eval.const
    · apply Value.Approx.Indexed.const
  case constr ctr_name =>
    exists Value.constr_app ctr_name []
    constructor
    · apply Eval.constr
    · apply Value.Approx.Indexed.constr_app
      intro k hk
      simp
  case app n n₁ n₂ env env₀ f body arg val val' hn hcl h₂ h₃ ih_f ih_arg ih_body =>
    have : env ≲ₑ'(m + n₂ + 1 + n₁) env' := by
      apply Env.Approx.Indexed'.anti_monotone
      · assumption
      · linarith
    obtain ⟨v_f, heval_f, happrox_f⟩ := ih_f (m + n₂ + 1) env' (by linarith) this
    clear this
    have : env ≲ₑ'(m + n₂ + n₁ + 1) env' := by
      apply Env.Approx.Indexed'.anti_monotone
      · assumption
      · linarith
    obtain ⟨v_arg, heval_arg, happrox_arg⟩ := ih_arg (m + n₂) env' (by nlinarith) this
    clear this
    invert happrox_f
    case closure cenv cbody ch =>
      have happrox_arg' : val ≲ᵥ(n₂ + m) v_arg := by
        have : m + n₂ = n₂ + m := by linarith
        rw [this] at happrox_arg
        exact happrox_arg
      obtain ⟨v_body, heval_body, happrox_body⟩ := ch n₂ m (by linarith) val v_arg val' happrox_arg' h₃
      exists v_body
      constructor
      · apply Eval.app
        · exact heval_f
        · exact heval_arg
        · exact heval_body
      · assumption
  case constr_app n₁ n₂ env₁ e₁ cname args arg v' hlt _ h₂ h₃ h₄ =>
    obtain ⟨v₁, heval_e₁, happrox_e₁⟩ := h₃ m env' (by linarith) h₁
    have : env₁ ≲ₑ'(m + n₂) env' := by
      apply Env.Approx.Indexed'.anti_monotone
      · assumption
      · linarith
    obtain ⟨v₂, heval_arg, happrox_arg⟩ := h₄ m env' (by linarith) this
    invert happrox_e₁
    case constr_app args_rev hargs =>
      exists (Value.constr_app cname (v₂ :: args_rev))
      constructor
      · apply Eval.constr_app
        · exact heval_e₁
        · exact heval_arg
      · apply Value.Approx.Indexed.constr_app
        intro k hk
        constructor
        · apply Value.Approx.Indexed.anti_monotone
          · exact happrox_arg
          · linarith
        · apply hargs
          linarith
  case binop n' env₁ op arg₁ arg₂ i₁ i₂ v₁ v₂ hv₁ hv₂ =>
    obtain ⟨v₁', heval₁, happrox₁⟩ := hv₁ m env' (by linarith) h₁
    obtain ⟨v₂', heval₂, happrox₂⟩ := hv₂ m env' (by linarith) h₁
    invert happrox₁
    invert happrox₂
    exists (Value.const (Constant.int (eval_binop_int op i₁ i₂)))
    constructor
    · apply Eval.binop
      · exact heval₁
      · exact heval₂
    · apply Value.Approx.Indexed.const
  case lambda n' env₁ name body =>
    exists (Value.closure env' body)
    constructor
    · apply Eval.lambda
    · apply Value.Approx.Indexed.closure
      intro n₁ n₂ hlt a₁ a₂ v₁ happrox heval
      have happrox_env : a₁ ∷ env₁ ≲ₑ'(n₁ + n₂) a₂ ∷ env' := by
        constructor
        · constructor
          exact happrox
        · apply Env.Approx.Indexed'.anti_monotone (n := m + n')
          · assumption
          · linarith
      apply ihk (n₁ + n₂ + 1) (by linarith) (m := n₂) (n := n₁)
      · linarith
      · have : n₁ + n₂ = n₂ + n₁ := by linarith
        rw [<- this]
        exact happrox_env
      · exact heval
  case save n' n₁ n₂ env₁ name e₁ e₂ val val' hle ha₁ ha₂ ih₁ ih₂ =>
    have : env₁ ≲ₑ'(m + n₂ + n₁) env' := by
      apply Env.Approx.Indexed'.anti_monotone
      · assumption
      · linarith
    obtain ⟨v₁, heval₁, happrox₁⟩ := ih₁ (m + n₂) env' (by linarith) this
    clear this
    have : val ∷ env₁ ≲ₑ'(m + n₂) v₁ ∷ env' := by
      constructor
      · apply Object.Approx.Indexed'.value
        · apply Value.Approx.Indexed.anti_monotone
          · exact happrox₁
          · linarith
      apply Env.Approx.Indexed'.anti_monotone
      · assumption
      · linarith
    obtain ⟨v₂, heval₂, happrox₂⟩ := ih₂ m (v₁ ∷ env') (by linarith) this
    exists v₂
    constructor
    · apply Eval.save
      · exact heval₁
      · exact heval₂
    · assumption
  case branch_matches e' n₁ n₁' env₁ name args_rev body val hlt heval_body ih =>
    rcases env' with
      ⟨⟩ | ⟨⟨hd⟩, env'⟩
    case nil =>
      cases h₁
    case cons.value =>
      cases h₁
      case cons h₁ h₂ =>
        cases h₁
        case value h₁ =>
          invert h₁
          case constr_app args_rev' happrox =>
            let args := List.map Object.value args_rev
            let args' := List.map Object.value args_rev'
            have : args ++ env₁ ≲ₑ'(m + n₁') args' ++ env' := by
              apply Env.Approx.Indexed'.concat
              · apply Env.Approx.Indexed'.from_value
                apply happrox
                linarith
              · apply Env.Approx.Indexed'.anti_monotone
                · assumption
                · linarith
            obtain ⟨v', heval', happrox'⟩ := ih m (args' ++ env') (by linarith) this
            exists v'
            constructor
            · apply Eval.branch_matches
              · exact heval'
            · assumption
    case cons.delayed =>
      cases h₁
      case cons h _ =>
        cases h
  case branch_fails e' n' env₁ name name' args e₂ v₂ hname heval ih =>
    rcases env' with
      ⟨⟩ | ⟨⟨hd⟩, env'⟩
    case nil =>
      cases h₁
    case cons.value =>
      cases h₁
      case cons h₁ h₂ =>
        cases h₁
        case value h₁ =>
          invert h₁
          case constr_app args_rev h =>
            have h₃ : Value.constr_app name args ∷ env₁ ≲ₑ'(m + n') Value.constr_app name args_rev ∷ env' := by
              constructor
              · apply Object.Approx.Indexed'.value
                apply Value.Approx.Indexed.constr_app
                intro k hk
                apply h
                exact hk
              · apply Env.Approx.Indexed'.anti_monotone
                · assumption
                · linarith
            obtain ⟨v', heval', happrox'⟩ := ih m (Value.constr_app name args_rev ∷ env') (by linarith) h₃
            exists v'
            constructor
            · apply Eval.branch_fails
              · exact hname
              · exact heval'
            · assumption
    case cons.delayed =>
      cases h₁
      case cons h _ =>
        cases h
  case recur n₁ n₂ env₁ name body val hn ha₁ ih =>
    let d := Object.delayed env₁ (Expr.recur name body)
    let d' := Object.delayed env' (Expr.recur name body)
    have : d ≲ₒ'(m + n₂) d' := by
      simp [d, d']
      apply Object.Approx.Indexed'.delayed_eq
      apply Env.Approx.Indexed'.anti_monotone
      · assumption
      · linarith
    have : d :: env₁ ≲ₑ'(m + n₂) d' :: env' := by
      apply Env.Approx.Indexed'.cons
      · assumption
      · apply Env.Approx.Indexed'.anti_monotone
        · assumption
        · linarith
    obtain ⟨v, heval, happrox⟩ := ih m (d' :: env') (by linarith) this
    exists v
    constructor
    · apply Eval.recur
      exact heval
    · assumption

lemma Value.Approx.Indexed.preserved' {k} : Preservation k := by
  suffices ∀ k' ≤ k, Preservation k' by
    aesop
  induction k with
  | zero =>
    intro k' hk'
    refine preserved_step ?_
    intro k hk
    linarith
  | succ k ih =>
    intro k' hk'
    cases hk'
    case succ.refl =>
      refine preserved_step ?_
      intro k' hk'
      apply ih
      linarith
    case succ.step =>
      apply ih
      simp_all only [Nat.le_eq]

theorem Value.Approx.Indexed.preserved :
  ∀ m n env env' e v,
    env ≲ₑ'(m + n) env' →
    env ⊢ e ↦(n) v →
    ∃ v', env' ⊢ e ↦ v' ∧ v ≲ᵥ(m) v' := by
  intros m n _ _ _ _
  apply Value.Approx.Indexed.preserved' (k := m + n + 1)
  linarith

mutual
  lemma Env.Approx.Indexed'.refl' {n env} (h : ∀ v, v ≲ᵥ(n) v) : env ≲ₑ'(n) env :=
    match env with
    | List.nil =>
      List.Forall₂.nil
    | List.cons hd tl =>
      List.Forall₂.cons (a := hd) (b := hd) (l₁ := tl) (l₂ := tl) (Object.Approx.Indexed'.refl' h) (Env.Approx.Indexed'.refl' h)

  lemma Object.Approx.Indexed'.refl' {n o} (h : ∀ v, v ≲ᵥ(n) v) : o ≲ₒ'(n) o := by
    cases o
    case value v =>
      apply Object.Approx.Indexed'.value
      apply h
    case delayed env e =>
      apply Object.Approx.Indexed'.delayed_eq
      exact Env.Approx.Indexed'.refl' h
end

@[refl]
lemma Value.Approx.Indexed.refl {n} v : v ≲ᵥ(n) v := by
  revert n
  suffices ∀ n, ∀ k ≤ n, v ≲ᵥ(k) v by
    intro k
    exact this k k k.le_refl
  intro n
  induction n generalizing v with
  | zero =>
    intros k hk
    cases v
    case unit =>
      exact Value.Approx.Indexed.unit
    case const c =>
      exact Value.Approx.Indexed.const
    case constr_app ctr_name args_rev =>
      apply Value.Approx.Indexed.constr_app
      · intros
        have : k = 0 := by linarith
        subst k
        contradiction
    case closure env body =>
      apply Value.Approx.Indexed.closure
      · intros
        have : k = 0 := by linarith
        subst k
        contradiction
  | succ n ih =>
    intros k hk
    cases v
    case unit =>
      exact Value.Approx.Indexed.unit
    case const c =>
      exact Value.Approx.Indexed.const
    case constr_app ctr_name args_rev =>
      apply Value.Approx.Indexed.constr_app
      · intros k' hk'
        have : k' ≤ n := by linarith
        rw [List.forall₂_same]
        intros
        apply ih
        · assumption
    case closure env body =>
      apply Value.Approx.Indexed.closure
      · intros n₁ n₂ hn a₁ a₂ r₁ happrox heval
        have henv : a₁ ∷ env ≲ₑ'(n₁ + n₂) a₂ ∷ env := by
          simp [Env.Approx.Indexed']
          constructor
          · constructor; exact happrox
          · intro x _
            cases x
            case value v₁ v₂ =>
              apply Object.Approx.Indexed'.value
              · apply ih
                · linarith
            case delayed =>
              apply Object.Approx.Indexed'.refl'
              intro v
              apply ih
              linarith
        apply Value.Approx.Indexed.preserved (n := n₁) (m := n₂)
        · have : n₁ + n₂ = n₂ + n₁ := by linarith
          rw [<- this]
          exact henv
        · assumption

@[refl]
lemma Env.Approx.Indexed'.refl {n env} : env ≲ₑ'(n) env :=
  Env.Approx.Indexed'.refl' Value.Approx.Indexed.refl

@[refl]
lemma Object.Approx.Indexed'.refl {n o} : o ≲ₒ'(n) o :=
  Object.Approx.Indexed'.refl' Value.Approx.Indexed.refl

end Juvix.Core.Main
