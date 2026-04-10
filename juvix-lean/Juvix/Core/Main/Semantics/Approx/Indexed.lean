
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

theorem Env.Approx.Indexed'.append_values {n : Nat} {args args' : List Value} {env env' : Env} : args ≲ₐ(n) args' → env ≲ₑ'(n) env' → args.map Object.value ++ env ≲ₑ'(n) args'.map Object.value ++ env' := by
  intro hargs henv
  exact Env.Approx.Indexed'.concat (Env.Approx.Indexed'.from_value hargs) henv

theorem Env.Approx.Indexed'.cons_constr_app {n : Nat} {name : Name} {args_rev args_rev' : List Value} {env env' : Env} : (∀ k < n, args_rev ≲ₐ(k) args_rev') → env ≲ₑ'(n) env' → Value.constr_app name args_rev ∷ env ≲ₑ'(n) Value.constr_app name args_rev' ∷ env' := by
  intro hargs henv
  exact Env.Approx.Indexed'.cons (Object.Approx.Indexed'.value (Value.Approx.Indexed.constr_app hargs)) henv

theorem Env.Approx.Indexed'.cons_delayed_eq {n : Nat} {env env' : Env} {e : Expr} : env ≲ₑ'(n) env' → Object.delayed env e :: env ≲ₑ'(n) Object.delayed env' e :: env' := by
  intro h
  exact List.Forall₂.cons (Object.Approx.Indexed'.delayed_eq h) h

theorem Env.Approx.Indexed'.cons_value {n : Nat} {v v' : Value} {env env' : Env} : v ≲ᵥ(n) v' → env ≲ₑ'(n) env' → v ∷ env ≲ₑ'(n) v' ∷ env' := by
  intro hv henv
  exact Env.Approx.Indexed'.cons (Object.Approx.Indexed'.value hv) henv

theorem Env.Approx.Indexed'.head_constr_app {n : Nat} {name : Name} {args_rev : List Value} {env env' : Env} : Value.constr_app name args_rev ∷ env ≲ₑ'(n) env' → ∃ args_rev' env'', env' = (Value.constr_app name args_rev' ∷ env'') ∧ env ≲ₑ'(n) env'' ∧ (∀ k < n, args_rev ≲ₐ(k) args_rev') := by
  intro henv
  cases henv with
  | cons hhd htl =>
      cases hhd with
      | value hv =>
          have hv' := Value.Approx.Indexed.invert hv
          cases hv' with
          | constr_app hargs =>
              refine ⟨_, _, ?_, htl, hargs⟩
              rfl

theorem Value.Approx.Indexed.apply_closure {n_body n_res : Nat} {a a' r : Value} {env env' : Env} {body body' : Expr} : Value.closure env body ≲ᵥ(n_body + n_res + 1) Value.closure env' body' → a ≲ᵥ(n_body + n_res) a' → a ∷ env ⊢ body ↦(n_body) r → ∃ r', a' ∷ env' ⊢ body' ↦ r' ∧ r ≲ᵥ(n_res) r' := by
  intro hcl ha he
  have hcl' := Value.Approx.Indexed.invert hcl
  cases hcl' with
  | closure h =>
      exact h n_body n_res (by omega) a a' r ha he

theorem Value.Approx.Indexed.closure_same_body_of_preservation {k m : Nat} {env env' : Env} {body : Expr} : (∀ k' < k, Preservation k') → m < k → env ≲ₑ'(m) env' → Value.closure env body ≲ᵥ(m) Value.closure env' body := by
  intro hprev hmk henv
  apply Value.Approx.Indexed.closure
  intro n₁ n₂ hlt a₁ a₂ r₁ ha he
  have hpres : Preservation m := hprev m hmk
  have ha' : a₁ ≲ᵥ(n₂ + n₁) a₂ := by
    simpa only [Nat.add_comm] using ha
  have henv'' : env ≲ₑ'(n₂ + n₁) env' :=
    Env.Approx.Indexed'.anti_monotone henv (by simpa only [Nat.add_comm] using Nat.le_of_lt hlt)
  have henv' : a₁ ∷ env ≲ₑ'(n₂ + n₁) a₂ ∷ env' :=
    Env.Approx.Indexed'.cons (Object.Approx.Indexed'.value ha') henv''
  exact hpres n₂ n₁ (a₁ ∷ env) (a₂ ∷ env') body r₁ (by simpa only [Nat.add_comm] using hlt) henv' he

theorem Value.Approx.Indexed.constr_app_cons {n : Nat} {ctr_name : Name} {args_rev args_rev' : List Value} {arg arg' : Value} : Value.constr_app ctr_name args_rev ≲ᵥ(n) Value.constr_app ctr_name args_rev' → arg ≲ᵥ(n) arg' → Value.constr_app ctr_name (arg :: args_rev) ≲ᵥ(n) Value.constr_app ctr_name (arg' :: args_rev') := by
  intro hctr harg
  have hinv := Value.Approx.Indexed.invert hctr
  cases hinv with
  | constr_app hargs =>
      apply Value.Approx.Indexed.constr_app
      intro k hk
      exact List.Forall₂.cons (Value.Approx.Indexed.anti_monotone harg (Nat.le_of_lt hk)) (hargs k hk)

theorem Value.Approx.Indexed.constr_app_shape {n : Nat} {ctr_name : Name} {args_rev : List Value} {v' : Value} : Value.constr_app ctr_name args_rev ≲ᵥ(n) v' → ∃ args_rev', v' = Value.constr_app ctr_name args_rev' ∧ (∀ k < n, args_rev ≲ₐ(k) args_rev') := by
  intro h
  have hinv := Value.Approx.Indexed.invert h
  cases hinv with
  | constr_app hargs =>
      exact ⟨_, rfl, hargs⟩

lemma Value.Approx.Indexed.preserved_step {k} :
  (∀ k' < k, Preservation k') → Preservation k := by
  intro hprev m n env env' e v hlt henv heval
  induction heval generalizing m env' with
  | var hlookup =>
      rcases Env.Approx.Indexed'.value henv hlookup with ⟨v', hlookup', hv⟩
      refine ⟨v', Eval.var hlookup', ?_⟩
      exact Value.Approx.Indexed.anti_monotone hv (by linarith)
  | var_rec hlookup heval ih =>
      rename_i n_cur env₀ name idx env₁ expr val
      rcases Env.Approx.Indexed'.delayed henv hlookup with hdelayed | hdelayed
      · rcases hdelayed with ⟨env₁', expr', hexpr, hlookup'⟩
        rcases hexpr n_cur m _ (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]) heval with ⟨v', heval', hv⟩
        exact ⟨v', Eval.var_rec hlookup' heval', hv⟩
      · rcases hdelayed with ⟨env₁', henv₁, hlookup'⟩
        rcases ih m env₁' hlt henv₁ with ⟨v', heval', hv⟩
        exact ⟨v', Eval.var_rec hlookup' heval', hv⟩
  | unit =>
      exact ⟨Value.unit, Eval.unit, Value.Approx.Indexed.unit⟩
  | const =>
      exact ⟨_, Eval.const, Value.Approx.Indexed.const⟩
  | constr =>
      refine ⟨_, Eval.constr, ?_⟩
      apply Value.Approx.Indexed.constr_app
      intro j hj
      exact List.Forall₂.nil
  | app hn hevalf hevala hevalbody ihf iha ihbody =>
      rename_i n_total n_fun n_body env₀ env_cl f body arg a r
      have hfun_lt : (m + n_body + 1) + n_fun < k := by linarith
      have hfun_env : env₀ ≲ₑ'((m + n_body + 1) + n_fun) env' := by
        exact Env.Approx.Indexed'.anti_monotone henv (by linarith)
      rcases ihf (m + n_body + 1) env' hfun_lt hfun_env with ⟨vf, hfunEval, hfunApprox⟩
      have harg_lt : (m + n_body) + (n_fun + 1) < k := by linarith
      have harg_env : env₀ ≲ₑ'((m + n_body) + (n_fun + 1)) env' := by
        exact Env.Approx.Indexed'.anti_monotone henv (by linarith)
      rcases iha (m + n_body) env' harg_lt harg_env with ⟨va, hargEval, hargApprox⟩
      have hfunApprox' : Value.closure env_cl body ≲ᵥ(n_body + m + 1) vf := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hfunApprox
      have hargApprox' : a ≲ᵥ(n_body + m) va := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hargApprox
      have hinv := Value.Approx.Indexed.invert hfunApprox'
      cases hinv with
      | closure happ =>
          rcases Value.Approx.Indexed.apply_closure (n_body := n_body) (n_res := m) hfunApprox' hargApprox' hevalbody with ⟨v', hbodyEval, hv⟩
          exact ⟨v', Eval.app hfunEval hargEval hbodyEval, hv⟩
  | constr_app hn hevalctr hevalarg ihctr iharg =>
      rename_i n_total n_arg env₀ ctr ctr_name ctr_args_rev arg val
      rcases ihctr m env' hlt henv with ⟨vctr', hctrEval, hctrApprox⟩
      rcases Value.Approx.Indexed.constr_app_shape hctrApprox with ⟨ctr_args_rev', rfl, hargs⟩
      have harg_lt : m + n_arg < k := by linarith
      have harg_env : env₀ ≲ₑ'(m + n_arg) env' := by
        exact Env.Approx.Indexed'.anti_monotone henv (by linarith)
      rcases iharg m env' harg_lt harg_env with ⟨varg', hargEval, hargApprox⟩
      refine ⟨Value.constr_app ctr_name (varg' :: ctr_args_rev'), Eval.constr_app hctrEval hargEval, ?_⟩
      have hctrApprox' : Value.constr_app ctr_name ctr_args_rev ≲ᵥ(m) Value.constr_app ctr_name ctr_args_rev' := by
        exact Value.Approx.Indexed.constr_app hargs
      exact Value.Approx.Indexed.constr_app_cons hctrApprox' hargApprox
  | binop heval1 heval2 ih1 ih2 =>
      rename_i n_cur env₀ op arg₁ arg₂ val₁ val₂
      rcases ih1 m env' hlt henv with ⟨v₁', heval₁', h₁approx⟩
      have h₁inv := Value.Approx.Indexed.invert h₁approx
      cases h₁inv with
      | const =>
          rcases ih2 m env' hlt henv with ⟨v₂', heval₂', h₂approx⟩
          have h₂inv := Value.Approx.Indexed.invert h₂approx
          cases h₂inv with
          | const =>
              exact ⟨_, Eval.binop heval₁' heval₂', Value.Approx.Indexed.const⟩
  | lambda =>
      refine ⟨_, Eval.lambda, ?_⟩
      apply Value.Approx.Indexed.closure_same_body_of_preservation hprev
      · linarith
      · exact Env.Approx.Indexed'.anti_monotone henv (by linarith)
  | save hn hevalvalue hevalbody ihvalue ihbody =>
      rename_i n_total n_value n_body env₀ name value body val val'
      have hvalue_lt : (m + n_body) + n_value < k := by linarith
      have hvalue_env : env₀ ≲ₑ'((m + n_body) + n_value) env' := by
        exact Env.Approx.Indexed'.anti_monotone henv (by linarith)
      rcases ihvalue (m + n_body) env' hvalue_lt hvalue_env with ⟨val₂, hvalueEval, hvalApprox⟩
      have henv_tail : env₀ ≲ₑ'(m + n_body) env' := by
        exact Env.Approx.Indexed'.anti_monotone henv (by linarith)
      have henv_body : val ∷ env₀ ≲ₑ'(m + n_body) val₂ ∷ env' := by
        exact Env.Approx.Indexed'.cons_value hvalApprox henv_tail
      have hbody_lt : m + n_body < k := by linarith
      rcases ihbody m ((val₂ ∷ env' : Env)) hbody_lt henv_body with ⟨v', hbodyEval, hv⟩
      exact ⟨v', Eval.save hvalueEval hbodyEval, hv⟩
  | branch_matches hn hevalbody ihbody =>
      rename_i n_total n_body env₀ name args_rev body val
      rcases Env.Approx.Indexed'.head_constr_app henv with ⟨args_rev', env₂, rfl, htail, hargs⟩
      have hargs' : args_rev ≲ₐ(m + n_body) args_rev' := by
        exact hargs (m + n_body) (by linarith)
      have htail' : env₀ ≲ₑ'(m + n_body) env₂ := by
        exact Env.Approx.Indexed'.anti_monotone htail (by linarith)
      have henv_body : args_rev.map Object.value ++ env₀ ≲ₑ'(m + n_body) args_rev'.map Object.value ++ env₂ := by
        exact Env.Approx.Indexed'.append_values hargs' htail'
      have hbody_lt : m + n_body < k := by linarith
      rcases ihbody m (args_rev'.map Object.value ++ env₂) hbody_lt henv_body with ⟨v', hbodyEval, hv⟩
      exact ⟨v', Eval.branch_matches hbodyEval, hv⟩
  | branch_fails hne hevalnext ihnext =>
      rename_i n_cur env₀ name name' args_rev next val
      rcases Env.Approx.Indexed'.head_constr_app henv with ⟨args_rev', env₂, rfl, htail, hargs⟩
      have henv_next : Value.constr_app name args_rev ∷ env₀ ≲ₑ'(m + n_cur) Value.constr_app name args_rev' ∷ env₂ := by
        exact Env.Approx.Indexed'.cons_constr_app hargs htail
      rcases ihnext m ((Value.constr_app name args_rev' ∷ env₂ : Env)) hlt henv_next with ⟨v', hnextEval, hv⟩
      exact ⟨v', Eval.branch_fails hne hnextEval, hv⟩
  | recur hn hevalbody ihbody =>
      rename_i n_total n_body env₀ name body val
      have henv_tail : env₀ ≲ₑ'(m + n_body) env' := by
        exact Env.Approx.Indexed'.anti_monotone henv (by linarith)
      have henv_body : Object.delayed env₀ (Expr.recur name body) :: env₀ ≲ₑ'(m + n_body) Object.delayed env' (Expr.recur name body) :: env' := by
        exact Env.Approx.Indexed'.cons_delayed_eq henv_tail
      have hbody_lt : m + n_body < k := by linarith
      rcases ihbody m (Object.delayed env' (Expr.recur name body) :: env') hbody_lt henv_body with ⟨v', hbodyEval, hv⟩
      exact ⟨v', Eval.recur hbodyEval, hv⟩


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
