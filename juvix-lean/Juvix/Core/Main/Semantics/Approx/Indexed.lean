
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

lemma Value.Approx.Indexed.anti_monotone {n n' v₁ v₂} (h : v₁ ≲ᵥ(n) v₂) (h' : n' ≤ n) : v₁ ≲ᵥ(n') v₂ := by sorry

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

theorem Env.Approx.Indexed'.append_values_anti {m n n' : Nat} {args args' : List Value} {env env' : Env} : (∀ k < m + n, args ≲ₐ(k) args') → n' < n → env ≲ₑ'(m + n) env' → args.map Object.value ++ env ≲ₑ'(m + n') args'.map Object.value ++ env' := by
  intro hargs hn' henv
  have hvals : args.map Object.value ≲ₑ'(m + n') args'.map Object.value := by
    apply Env.Approx.Indexed'.from_value
    exact hargs (m + n') (by omega)
  have henv' : env ≲ₑ'(m + n') env' := by
    exact Env.Approx.Indexed'.anti_monotone henv (by omega)
  exact Env.Approx.Indexed'.concat hvals henv'

theorem Env.Approx.Indexed'.cons_constr_inv {n : Nat} {name : Name} {args : List Value} {env env' : Env} : Object.value (Value.constr_app name args) :: env ≲ₑ'(n) env' → ∃ args' env'', env' = Object.value (Value.constr_app name args') :: env'' ∧ (∀ k < n, args ≲ₐ(k) args') ∧ env ≲ₑ'(n) env'' := by
  intro h
  cases h with
  | cons hhead htail =>
      cases hhead with
      | value hv =>
          cases Value.Approx.Indexed.invert hv with
          | constr_app hargs =>
              exact ⟨_, _, rfl, hargs, htail⟩

theorem Env.Approx.Indexed'.cons_recur_delayed_anti {m n n' : Nat} {env env' : Env} {name : Name} {body : Expr} : n' < n → env ≲ₑ'(m + n) env' → Object.delayed env (Expr.recur name body) :: env ≲ₑ'(m + n') Object.delayed env' (Expr.recur name body) :: env' := by
  intro hn henv
  have henv' : env ≲ₑ'(m + n') env' :=
    Env.Approx.Indexed'.anti_monotone henv (by omega)
  have hobj : Object.delayed env (Expr.recur name body) ≲ₒ'(m + n') Object.delayed env' (Expr.recur name body) :=
    Object.Approx.Indexed'.delayed_eq henv'
  exact Env.Approx.Indexed'.cons hobj henv'

theorem Env.Approx.Indexed'.cons_value_anti {m n : Nat} {v v' : Value} {env env' : Env} : v ≲ᵥ(m + n) v' → env ≲ₑ'(m + n) env' → v ∷ env ≲ₑ'(m) v' ∷ env' := by
  intro hv henv
  have hv' : v ≲ᵥ(m) v' := Value.Approx.Indexed.anti_monotone hv (Nat.le_add_right _ _)
  have henv' : env ≲ₑ'(m) env' := Env.Approx.Indexed'.anti_monotone henv (Nat.le_add_right _ _)
  exact Env.Approx.Indexed'.cons (Object.Approx.Indexed'.value hv') henv'

theorem Value.Approx.Indexed.closure_same_body {k m : Nat} {env env' : Env} {body : Expr} : (∀ k' < k, Preservation k') → m < k → env ≲ₑ'(m) env' → Value.closure env body ≲ᵥ(m) Value.closure env' body := by
  intro ihk hmk henv
  apply Value.Approx.Indexed.closure
  intro n₁ n₂ hlt a₁ a₂ r₁ ha heval
  have henv_cons : a₁ ∷ env ≲ₑ'(n₁ + n₂) a₂ ∷ env' := by
    apply Env.Approx.Indexed'.cons
    · exact Object.Approx.Indexed'.value ha
    · exact Env.Approx.Indexed'.anti_monotone henv (Nat.le_of_lt hlt)
  have hk' : n₁ + n₂ + 1 < k := by
    exact lt_of_le_of_lt (Nat.succ_le_of_lt hlt) hmk
  have hpres : Preservation (n₁ + n₂ + 1) := ihk (n₁ + n₂ + 1) hk'
  have hsmall : n₂ + n₁ < n₁ + n₂ + 1 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Nat.lt_succ_self (n₁ + n₂)
  have henv_cons' : a₁ ∷ env ≲ₑ'(n₂ + n₁) a₂ ∷ env' := by
    simpa [Nat.add_comm] using henv_cons
  obtain ⟨r₂, hr₂eval, hr₂approx⟩ := hpres n₂ n₁ (a₁ ∷ env) (a₂ ∷ env') body r₁ hsmall henv_cons' heval
  exact ⟨r₂, hr₂eval, hr₂approx⟩

lemma Value.Approx.Indexed.preserved_step {k} :
  (∀ k' < k, Preservation k') → Preservation k := by
  intro ihk m n env env' e v hmn henv heval
  induction heval generalizing m env' with
  | var hlookup =>
      rename_i n0 env0 name idx val
      obtain ⟨v', hlookup', happrox⟩ := Env.Approx.Indexed'.value henv hlookup
      refine ⟨v', ?_, ?_⟩
      · exact Eval.var hlookup'
      · exact Value.Approx.Indexed.anti_monotone happrox (Nat.le_add_right m n0)
  | var_rec hlookup hrec ih =>
      rename_i n0 env0 name idx envrec expr val
      rcases Env.Approx.Indexed'.delayed henv hlookup with hdelay | hdelay
      · rcases hdelay with ⟨env₂, e₂, hexpr, hlookup'⟩
        have hle' : n0 + m ≤ m + n0 := by
          exact le_of_eq (Nat.add_comm n0 m)
        obtain ⟨v', heval', happrox'⟩ := hexpr n0 m _ hle' hrec
        refine ⟨v', ?_, happrox'⟩
        exact Eval.var_rec hlookup' heval'
      · rcases hdelay with ⟨env₂, henv₂, hlookup'⟩
        obtain ⟨v', heval', happrox'⟩ := ih m env₂ hmn henv₂
        refine ⟨v', ?_, happrox'⟩
        exact Eval.var_rec hlookup' heval'
  | unit =>
      rename_i n0 env0
      refine ⟨_, Eval.unit, Value.Approx.Indexed.unit⟩
  | const =>
      rename_i n0 env0 c
      refine ⟨_, Eval.const, Value.Approx.Indexed.const⟩
  | constr =>
      rename_i n0 env0 name
      refine ⟨_, Eval.constr, ?_⟩
      apply Value.Approx.Indexed.constr_app
      intro k hk
      exact List.Forall₂.nil
  | app hle hfun harg hbody ih_fun ih_arg ih_body =>
      rename_i n0 n1 n2 env0 envclo f body arg argval res
      have henv_fun : env0 ≲ₑ'((m + n2 + 1) + n1) env' :=
        Env.Approx.Indexed'.anti_monotone henv (by linarith)
      obtain ⟨v_fun', heval_fun', happrox_fun'⟩ := ih_fun (m + n2 + 1) env' (by linarith) henv_fun
      invert happrox_fun'
      case closure envclo' body' hclo =>
        have henv_arg : env0 ≲ₑ'((m + n2) + (n1 + 1)) env' :=
          Env.Approx.Indexed'.anti_monotone henv (by linarith)
        obtain ⟨v_arg', heval_arg', happrox_arg'⟩ := ih_arg (m + n2) env' (by linarith) henv_arg
        have happrox_arg'' : argval ≲ᵥ(n2 + m) v_arg' := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using happrox_arg'
        have hlt' : n2 + m < m + n2 + 1 := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Nat.lt_succ_self (m + n2)
        obtain ⟨v'', heval_body', happrox'⟩ := hclo n2 m hlt' argval v_arg' res happrox_arg'' hbody
        refine ⟨v'', ?_, happrox'⟩
        exact Eval.app heval_fun' heval_arg' heval_body'
  | constr_app hlt hctr harg ih_ctr ih_arg =>
      rename_i n0 n1 env0 ctr ctr_name ctr_args_rev arg val
      obtain ⟨v_ctr', heval_ctr', happrox_ctr'⟩ := ih_ctr m env' hmn henv
      invert happrox_ctr'
      case constr_app ctr_args_rev' hargs =>
        have henv_arg : env0 ≲ₑ'(m + n1) env' :=
          Env.Approx.Indexed'.anti_monotone henv (by linarith)
        obtain ⟨v_arg', heval_arg', happrox_arg'⟩ := ih_arg m env' (by linarith) henv_arg
        refine ⟨Value.constr_app ctr_name (v_arg' :: ctr_args_rev'), ?_, ?_⟩
        · exact Eval.constr_app heval_ctr' heval_arg'
        · apply Value.Approx.Indexed.constr_app
          intro k hk
          refine List.Forall₂.cons ?_ (hargs k hk)
          exact Value.Approx.Indexed.anti_monotone happrox_arg' (Nat.le_of_lt hk)
  | binop h₁ h₂ ih₁ ih₂ =>
      rename_i n0 env0 op arg₁ arg₂ val₁ val₂
      obtain ⟨v₁', heval₁', happrox₁'⟩ := ih₁ m env' hmn henv
      invert happrox₁'
      obtain ⟨v₂', heval₂', happrox₂'⟩ := ih₂ m env' hmn henv
      invert happrox₂'
      refine ⟨_, ?_, Value.Approx.Indexed.const⟩
      exact Eval.binop heval₁' heval₂'
  | lambda =>
      rename_i n0 env0 name body
      refine ⟨_, Eval.lambda, ?_⟩
      apply Value.Approx.Indexed.closure_same_body ihk
      · exact lt_of_le_of_lt (Nat.le_add_right m n0) hmn
      · exact Env.Approx.Indexed'.anti_monotone henv (Nat.le_add_right m n0)
  | save hle hval hbody ih_val ih_body =>
      rename_i n0 n1 n2 env0 name value body val res
      have henv_val : env0 ≲ₑ'((m + n2) + n1) env' :=
        Env.Approx.Indexed'.anti_monotone henv (by linarith)
      obtain ⟨v', heval_val', happrox_val'⟩ := ih_val (m + n2) env' (by linarith) henv_val
      have henv_tail : env0 ≲ₑ'(m + n2) env' :=
        Env.Approx.Indexed'.anti_monotone henv (by linarith)
      have henv_body : val ∷ env0 ≲ₑ'(m + n2) v' ∷ env' := by
        apply Env.Approx.Indexed'.cons
        · exact Object.Approx.Indexed'.value happrox_val'
        · exact henv_tail
      obtain ⟨v'', heval_body', happrox'⟩ := ih_body m (v' ∷ env') (by linarith) henv_body
      refine ⟨v'', ?_, happrox'⟩
      exact Eval.save heval_val' heval_body'
  | branch_matches hlt hbody ih_body =>
      rename_i n0 n1 env0 name args_rev body val
      rcases Env.Approx.Indexed'.cons_constr_inv henv with ⟨args_rev', env2, rfl, hargs, htail⟩
      have henv_body : args_rev.map Object.value ++ env0 ≲ₑ'(m + n1) args_rev'.map Object.value ++ env2 :=
        Env.Approx.Indexed'.append_values_anti (m := m) (n := n0) (n' := n1) hargs hlt htail
      obtain ⟨v', heval', happrox'⟩ := ih_body m (args_rev'.map Object.value ++ env2) (by linarith) henv_body
      refine ⟨v', ?_, happrox'⟩
      exact Eval.branch_matches heval'
  | branch_fails hneq hnext ih_next =>
      rename_i n0 env0 name name' args_rev next val
      rcases Env.Approx.Indexed'.cons_constr_inv henv with ⟨args_rev', env2, rfl, hargs, htail⟩
      have henv_next : Value.constr_app name args_rev ∷ env0 ≲ₑ'(m + n0) Value.constr_app name args_rev' ∷ env2 := by
        apply Env.Approx.Indexed'.cons
        · exact Object.Approx.Indexed'.value (Value.Approx.Indexed.constr_app hargs)
        · exact htail
      obtain ⟨v', heval', happrox'⟩ := ih_next m (Value.constr_app name args_rev' ∷ env2) hmn henv_next
      refine ⟨v', ?_, happrox'⟩
      exact Eval.branch_fails hneq heval'
  | recur hlt hbody ih_body =>
      rename_i n0 n1 env0 name body val
      have henv_body : Object.delayed env0 (Expr.recur name body) :: env0 ≲ₑ'(m + n1) Object.delayed env' (Expr.recur name body) :: env' :=
        Env.Approx.Indexed'.cons_recur_delayed_anti (m := m) (n := n0) (n' := n1) hlt henv
      obtain ⟨v', heval', happrox'⟩ := ih_body m (Object.delayed env' (Expr.recur name body) :: env') (by linarith) henv_body
      refine ⟨v', ?_, happrox'⟩
      exact Eval.recur heval'


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
lemma Value.Approx.Indexed.refl {n} v : v ≲ᵥ(n) v := by sorry

@[refl]
lemma Env.Approx.Indexed'.refl {n env} : env ≲ₑ'(n) env :=
  Env.Approx.Indexed'.refl' Value.Approx.Indexed.refl

@[refl]
lemma Object.Approx.Indexed'.refl {n o} : o ≲ₒ'(n) o :=
  Object.Approx.Indexed'.refl' Value.Approx.Indexed.refl

end Juvix.Core.Main
