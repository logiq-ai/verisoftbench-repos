
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

lemma Value.Approx.Indexed.anti_monotone {n n' v₁ v₂} (h : v₁ ≲ᵥ(n) v₂) (h' : n' ≤ n) : v₁ ≲ᵥ(n') v₂ := by
  revert n n'
  suffices ∀ n, v₁ ≲ᵥ(n) v₂ → ∀ k ≤ n, v₁ ≲ᵥ(k) v₂ by
    intro n n' h hn
    exact this n h n' hn
  intro n
  induction n generalizing v₁ v₂ with
  | zero =>
    intros h k hk
    invert h
    case unit =>
      exact Value.Approx.Indexed.unit
    case const =>
      exact Value.Approx.Indexed.const
    case constr_app ctr_name args_rev args_rev' hargs =>
      apply Value.Approx.Indexed.constr_app
      · intros
        have : k = 0 := by linarith
        subst k
        contradiction
    case closure env₁ body₁ env₂ body₂ h =>
      apply Value.Approx.Indexed.closure
      · intros
        have : k = 0 := by linarith
        subst k
        contradiction
  | succ n ih =>
    intros h k hk
    invert h
    case unit =>
      exact Value.Approx.Indexed.unit
    case const =>
      exact Value.Approx.Indexed.const
    case constr_app ctr_name args_rev args_rev' hargs =>
      apply Value.Approx.Indexed.constr_app
      · intros k' hk'
        have : k' < n + 1 := by linarith
        simp_all only
    case closure env₁ body₁ env₂ body₂ ch =>
      apply Value.Approx.Indexed.closure
      · intro n₁ n₂ hn a₁ a₂ v₁ happrox heval
        apply ch n₁ n₂
        · linarith
        · assumption
        · assumption

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

theorem Value.Approx.Indexed.preserved_step {k : Nat} : (∀ k' < k, Value.Approx.Indexed.Preservation k') → Value.Approx.Indexed.Preservation k := by
  intro ihk m n env env' e v hk henv hev
  induction hev generalizing m env'
  case var h =>
    obtain ⟨v', hget, happrox⟩ := Env.Approx.Indexed'.value henv h
    refine ⟨v', Eval.var hget, ?_⟩
    apply Value.Approx.Indexed.anti_monotone happrox
    linarith
  case var_rec n env name idx env₁ expr val hget heval ih =>
    rcases Env.Approx.Indexed'.delayed henv hget with ⟨env₂', e₂', hexpr, hget'⟩ | ⟨env₂, henv₂, hget'⟩
    · simp only [Expr.Approx.Param.Indexed] at hexpr
      obtain ⟨v'', heval', happrox'⟩ := hexpr n m val (by linarith) heval
      exact ⟨v'', Eval.var_rec hget' heval', happrox'⟩
    · obtain ⟨v'', heval', happrox'⟩ := ih m env₂ (by linarith) henv₂
      exact ⟨v'', Eval.var_rec hget' heval', happrox'⟩
  case unit =>
    exact ⟨Value.unit, Eval.unit, Value.Approx.Indexed.unit⟩
  case const n env c =>
    exact ⟨Value.const c, Eval.const, Value.Approx.Indexed.const⟩
  case constr n env name =>
    refine ⟨Value.constr_app name [], Eval.constr, ?_⟩
    apply Value.Approx.Indexed.constr_app
    intro k hk
    simp
  case app n n₁ n₂ env env₁ f body arg val val' hn heval_f heval_arg heval_body ih_f ih_arg ih_body =>
    have henv_f : env ≲ₑ'(m + n₂ + 1 + n₁) env' := by
      apply Env.Approx.Indexed'.anti_monotone henv
      linarith
    obtain ⟨v_f, heval_f', happrox_f⟩ := ih_f (m + n₂ + 1) env' (by linarith) henv_f
    have henv_arg : env ≲ₑ'(m + n₂ + (n₁ + 1)) env' := by
      apply Env.Approx.Indexed'.anti_monotone henv
      linarith
    obtain ⟨v_arg, heval_arg', happrox_arg⟩ := ih_arg (m + n₂) env' (by linarith) henv_arg
    invert happrox_f
    case closure ch =>
      have hcomm : m + n₂ = n₂ + m := by linarith
      rw [hcomm] at happrox_arg
      obtain ⟨v_body, heval_body', happrox_body⟩ := ch n₂ m (by linarith) val v_arg val' happrox_arg heval_body
      exact ⟨v_body, Eval.app heval_f' heval_arg' heval_body', happrox_body⟩
  case constr_app n n' env ctr ctr_name ctr_args_rev arg val hlt heval_ctr heval_arg ih_ctr ih_arg =>
    obtain ⟨v_ctr, heval_ctr', happrox_ctr⟩ := ih_ctr m env' hk henv
    have henv_arg : env ≲ₑ'(m + n') env' := by
      apply Env.Approx.Indexed'.anti_monotone henv
      linarith
    obtain ⟨v_arg, heval_arg', happrox_arg⟩ := ih_arg m env' (by linarith) henv_arg
    invert happrox_ctr
    case constr_app args_rev' hargs =>
      refine ⟨Value.constr_app ctr_name (v_arg :: args_rev'), Eval.constr_app heval_ctr' heval_arg', ?_⟩
      apply Value.Approx.Indexed.constr_app
      intro k hk'
      constructor
      · exact Value.Approx.Indexed.anti_monotone happrox_arg (by linarith)
      · exact hargs k hk'
  case binop n env op arg₁ arg₂ val₁ val₂ heval₁ heval₂ ih₁ ih₂ =>
    obtain ⟨v₁', heval₁', happrox₁⟩ := ih₁ m env' hk henv
    obtain ⟨v₂', heval₂', happrox₂⟩ := ih₂ m env' hk henv
    invert happrox₁
    case const =>
      invert happrox₂
      case const =>
        exact ⟨Value.const (Constant.int (eval_binop_int op val₁ val₂)), Eval.binop heval₁' heval₂', Value.Approx.Indexed.const⟩
  case lambda n env name body =>
    refine ⟨Value.closure env' body, Eval.lambda, ?_⟩
    apply Value.Approx.Indexed.closure
    intro n₁ n₂ hlt a₁ a₂ v₁ happrox heval
    have happrox_env : a₁ ∷ env ≲ₑ'(n₁ + n₂) a₂ ∷ env' := by
      apply Env.Approx.Indexed'.cons
      · exact Object.Approx.Indexed'.value happrox
      · apply Env.Approx.Indexed'.anti_monotone henv
        linarith
    have hk' : n₁ + n₂ + 1 < k := by
      linarith
    have hpres := ihk (n₁ + n₂ + 1) hk'
    have hcomm : n₁ + n₂ = n₂ + n₁ := by linarith
    rw [hcomm] at happrox_env
    exact hpres n₂ n₁ (a₁ ∷ env) (a₂ ∷ env') body v₁ (by linarith) happrox_env heval
  case save n n₁ n₂ env name value body val val' hle heval_val heval_body ih_val ih_body =>
    have henv_val : env ≲ₑ'(m + n₂ + n₁) env' := by
      apply Env.Approx.Indexed'.anti_monotone henv
      linarith
    obtain ⟨v₁, heval₁, happrox₁⟩ := ih_val (m + n₂) env' (by linarith) henv_val
    have henv_body : val ∷ env ≲ₑ'(m + n₂) v₁ ∷ env' := by
      apply Env.Approx.Indexed'.cons
      · exact Object.Approx.Indexed'.value happrox₁
      · apply Env.Approx.Indexed'.anti_monotone henv
        linarith
    obtain ⟨v₂, heval₂, happrox₂⟩ := ih_body m (v₁ ∷ env') (by linarith) henv_body
    exact ⟨v₂, Eval.save heval₁ heval₂, happrox₂⟩
  case branch_matches next n n' env name args_rev body val hlt heval_body ih =>
    cases env' with
    | nil =>
        cases henv
    | cons hd env' =>
        cases henv with
        | cons hhd htail =>
            cases hd with
            | value vhd =>
                cases hhd with
                | value happrox_head =>
                    invert happrox_head
                    case constr_app args_rev' hargs =>
                      have henv_body : List.map Object.value args_rev ++ env ≲ₑ'(m + n') List.map Object.value args_rev' ++ env' := by
                        apply Env.Approx.Indexed'.concat
                        · apply Env.Approx.Indexed'.from_value
                          exact hargs (m + n') (by linarith)
                        · apply Env.Approx.Indexed'.anti_monotone htail
                          linarith
                      obtain ⟨v', heval', happrox'⟩ := ih m (List.map Object.value args_rev' ++ env') (by linarith) henv_body
                      exact ⟨v', Eval.branch_matches heval', happrox'⟩
            | delayed env₂ e₂ =>
                cases hhd
  case branch_fails body n env name name' args_rev next val hname heval ih =>
    cases env' with
    | nil =>
        cases henv
    | cons hd env' =>
        cases henv with
        | cons hhd htail =>
            cases hd with
            | value vhd =>
                cases hhd with
                | value happrox_head =>
                    invert happrox_head
                    case constr_app args_rev' hargs =>
                      have henv_next : Value.constr_app name args_rev ∷ env ≲ₑ'(m + n) Value.constr_app name args_rev' ∷ env' := by
                        apply Env.Approx.Indexed'.cons
                        · apply Object.Approx.Indexed'.value
                          apply Value.Approx.Indexed.constr_app
                          intro k hk'
                          exact hargs k hk'
                        · exact htail
                      obtain ⟨v', heval', happrox'⟩ := ih m (Value.constr_app name args_rev' ∷ env') hk henv_next
                      exact ⟨v', Eval.branch_fails hname heval', happrox'⟩
            | delayed env₂ e₂ =>
                cases hhd
  case recur n n' env name body val hlt heval_body ih_body =>
    let d := Object.delayed env (Expr.recur name body)
    let d' := Object.delayed env' (Expr.recur name body)
    have hd : d ≲ₒ'(m + n') d' := by
      apply Object.Approx.Indexed'.delayed_eq
      apply Env.Approx.Indexed'.anti_monotone henv
      linarith
    have henv_body : d :: env ≲ₑ'(m + n') d' :: env' := by
      apply Env.Approx.Indexed'.cons hd
      apply Env.Approx.Indexed'.anti_monotone henv
      linarith
    obtain ⟨v', heval', happrox'⟩ := ih_body m (d' :: env') (by linarith) henv_body
    exact ⟨v', Eval.recur heval', happrox'⟩


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
