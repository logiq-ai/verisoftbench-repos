
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

theorem EnvApproxIndexedAntiMonotoneAux: ∀ {n n' : Nat} {env₁ env₂ : Env}, env₁ ≲ₑ'(n) env₂ → n' ≤ n → env₁ ≲ₑ'(n') env₂ := by
  intro n n' env₁ env₂ h hle
  exact Env.Approx.Indexed'.anti_monotone h hle

theorem ValueApproxIndexedAntiMonotoneAux: ∀ {n n' : Nat} {v₁ v₂ : Value}, v₁ ≲ᵥ(n) v₂ → n' ≤ n → v₁ ≲ᵥ(n') v₂ := by
  intro n n' v₁ v₂ h hle
  have hinv := Value.Approx.Indexed.invert h
  cases hinv with
  | unit =>
      exact Value.Approx.Indexed.unit
  | const =>
      exact Value.Approx.Indexed.const
  | @constr_app ctr_name args_rev args_rev' hargs =>
      apply Value.Approx.Indexed.constr_app
      intro k hk
      exact hargs k (lt_of_lt_of_le hk hle)
  | @closure env₁ body₁ env₂ body₂ hbody =>
      apply Value.Approx.Indexed.closure
      intro n₁ n₂ hlt a₁ a₂ r₁ happ hEval
      exact hbody n₁ n₂ (lt_of_lt_of_le hlt hle) a₁ a₂ r₁ happ hEval

theorem Value.Approx.Indexed.preserved_step: ∀ {k : Nat}, (∀ k' < k, Preservation k') → Preservation k := by
  intro k hstep m n env env' e v hk henv heval
  induction heval generalizing m env' with
  | @branch_matches vars next n n' env name argsRev body val hn hbody ihbody =>
      cases henv with
      | @cons hd1 hd2 tl1 tl2 hhead htail =>
          cases hhead with
          | value happrox =>
              have hinv := Value.Approx.Indexed.invert happrox
              cases hinv with
              | constr_app hargs =>
                  have hargsBody := hargs (m + n') (by linarith)
                  have htail' : env ≲ₑ'(m + n') tl2 :=
                    EnvApproxIndexedAntiMonotoneAux htail (by linarith)
                  have henvBody :=
                    Env.Approx.Indexed'.concat (Env.Approx.Indexed'.from_value hargsBody) htail'
                  rcases ihbody m _ (by linarith) henvBody with ⟨v', hbody', hvalapprox⟩
                  exact ⟨v', Eval.branch_matches hbody', hvalapprox⟩
  | @branch_fails vars body n env name name' argsRev next val hneq hnext ihnext =>
      cases henv with
      | @cons hd1 hd2 tl1 tl2 hhead htail =>
          cases hhead with
          | value happrox =>
              have hinv := Value.Approx.Indexed.invert happrox
              cases hinv with
              | constr_app hargs =>
                  have henvWhole :=
                    Env.Approx.Indexed'.cons (Object.Approx.Indexed'.value happrox) htail
                  rcases ihnext m _ hk henvWhole with ⟨v', hnext', hvalapprox⟩
                  exact ⟨v', Eval.branch_fails hneq hnext', hvalapprox⟩
  | var hlookup =>
      obtain ⟨v', hlookup', happrox⟩ := Env.Approx.Indexed'.value henv hlookup
      refine ⟨v', ?_, ?_⟩
      · exact Eval.var hlookup'
      · exact ValueApproxIndexedAntiMonotoneAux happrox (by linarith)
  | @var_rec n env name idx envStored expr val hlookup heval ih =>
      have hdelayed := Env.Approx.Indexed'.delayed henv hlookup
      cases hdelayed with
      | inl hdel =>
          rcases hdel with ⟨envStored', expr', happrox, hlookup'⟩
          simp [Expr.Approx.Param.Indexed] at happrox
          rcases happrox n m val (by linarith) heval with ⟨v', heval', hvalapprox⟩
          exact ⟨v', Eval.var_rec hlookup' heval', hvalapprox⟩
      | inr hdel =>
          rcases hdel with ⟨envStored', henvStored', hlookup'⟩
          rcases ih m envStored' hk henvStored' with ⟨v', heval', hvalapprox⟩
          exact ⟨v', Eval.var_rec hlookup' heval', hvalapprox⟩
  | unit =>
      exact ⟨Value.unit, Eval.unit, Value.Approx.Indexed.unit⟩
  | const =>
      aesop
  | constr =>
      aesop
  | @app n n₁ n₂ env envCl f body arg val res hle hfun harg hbody ihfun iharg ihbody =>
      have henvFun : env ≲ₑ'((n₂ + m + 1) + n₁) env' :=
        EnvApproxIndexedAntiMonotoneAux henv (by linarith)
      rcases ihfun (n₂ + m + 1) env' (by linarith) henvFun with ⟨vfun', hfun', hfunapprox⟩
      invert hfunapprox
      case closure hcl =>
        have henvArg : env ≲ₑ'((n₂ + m) + (n₁ + 1)) env' :=
          EnvApproxIndexedAntiMonotoneAux henv (by linarith)
        rcases iharg (n₂ + m) env' (by linarith) henvArg with ⟨varg', harg', hargapprox⟩
        rcases hcl n₂ m (by linarith) val varg' res hargapprox hbody with ⟨vres', hbody', hresapprox⟩
        exact ⟨vres', Eval.app hfun' harg' hbody', hresapprox⟩
  | @constr_app n n' env ctr ctr_name ctrArgsRev arg val hn hctr harg ihctr iharg =>
      rcases ihctr m env' hk henv with ⟨vctr', hctr', hctrapprox⟩
      invert hctrapprox
      case constr_app hargs =>
        have henvArg : env ≲ₑ'(m + n') env' :=
          EnvApproxIndexedAntiMonotoneAux henv (by linarith)
        rcases iharg m env' (by linarith) henvArg with ⟨varg', harg', hargapprox⟩
        refine ⟨_, Eval.constr_app hctr' harg', ?_⟩
        apply Value.Approx.Indexed.constr_app
        intro i hi
        exact List.Forall₂.cons
          (ValueApproxIndexedAntiMonotoneAux hargapprox (by linarith))
          (hargs i hi)
  | @binop n env op arg₁ arg₂ val₁ val₂ harg₁ harg₂ ih₁ ih₂ =>
      rcases ih₁ m env' hk henv with ⟨v₁', harg₁', happrox₁⟩
      invert happrox₁
      case const =>
        rcases ih₂ m env' hk henv with ⟨v₂', harg₂', happrox₂⟩
        invert happrox₂
        case const =>
          exact ⟨_, Eval.binop harg₁' harg₂', Value.Approx.Indexed.const⟩
  | @lambda n env name body =>
      refine ⟨Value.closure env' body, Eval.lambda, ?_⟩
      apply Value.Approx.Indexed.closure
      intro n₁ n₂ hnlt a₁ a₂ r₁ ha happ
      have henvTail : env ≲ₑ'(n₁ + n₂) env' :=
        EnvApproxIndexedAntiMonotoneAux henv (by linarith)
      have henvCons : a₁ ∷ env ≲ₑ'(n₁ + n₂) a₂ ∷ env' :=
        Env.Approx.Indexed'.cons (Object.Approx.Indexed'.value ha) henvTail
      have henvCons' : a₁ ∷ env ≲ₑ'(n₂ + n₁) a₂ ∷ env' := by
        simpa [Nat.add_comm] using henvCons
      have hsmall : n₁ + n₂ + 1 < k := by
        linarith
      have hpres := hstep (n₁ + n₂ + 1) hsmall
      exact hpres n₂ n₁ (a₁ ∷ env) (a₂ ∷ env') body r₁ (by linarith) henvCons' happ
  | @save n n₁ n₂ env name value body val res hle hval hbody ihval ihbody =>
      have henvVal : env ≲ₑ'((n₂ + m) + n₁) env' :=
        EnvApproxIndexedAntiMonotoneAux henv (by linarith)
      rcases ihval (n₂ + m) env' (by linarith) henvVal with ⟨vval', hval', hvalapprox⟩
      have henvTail : env ≲ₑ'(n₂ + m) env' :=
        EnvApproxIndexedAntiMonotoneAux henv (by linarith)
      have henvBody : val ∷ env ≲ₑ'(m + n₂) vval' ∷ env' := by
        simpa [Nat.add_comm] using Env.Approx.Indexed'.cons (Object.Approx.Indexed'.value hvalapprox) henvTail
      rcases ihbody m (vval' ∷ env') (by linarith) henvBody with ⟨vres', hbody', hresapprox⟩
      exact ⟨vres', Eval.save hval' hbody', hresapprox⟩
  | @recur n n' env name body val hn hbody ihbody =>
      have henvTail : env ≲ₑ'(m + n') env' :=
        EnvApproxIndexedAntiMonotoneAux henv (by linarith)
      have hhead : Object.delayed env (Expr.recur name body) ≲ₒ'(m + n') Object.delayed env' (Expr.recur name body) :=
        Object.Approx.Indexed'.delayed_eq henvTail
      have henvBody :
          Object.delayed env (Expr.recur name body) :: env ≲ₑ'(m + n')
            Object.delayed env' (Expr.recur name body) :: env' :=
        Env.Approx.Indexed'.cons hhead henvTail
      rcases ihbody m (Object.delayed env' (Expr.recur name body) :: env') (by linarith) henvBody with
        ⟨v', hbody', hvalapprox⟩
      exact ⟨v', Eval.recur hbody', hvalapprox⟩


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
