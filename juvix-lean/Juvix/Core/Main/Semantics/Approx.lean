
import Juvix.Core.Main.Semantics.Approx.Indexed

namespace Juvix.Core.Main

def Value.Approx (v v' : Value) : Prop :=
  ∀ n, v ≲ᵥ(n) v'

notation:40 v:40 " ≲ᵥ " v':40 => Value.Approx v v'

notation:40 args₁:40 " ≲ₐ " args₂:40 => List.Forall₂ Value.Approx args₁ args₂

def Expr.Approx.Param (env₁ env₂ : Env) (e₁ e₂ : Expr) : Prop :=
  (∀ v₁, env₁ ⊢ e₁ ↦ v₁ → ∃ v₂, env₂ ⊢ e₂ ↦ v₂ ∧ v₁ ≲ᵥ v₂)

notation:40 e:40 " ≲⟨" env:40 ", " env':40 "⟩ " e':40 => Expr.Approx.Param env env' e e'

inductive Object.Approx : Object → Object → Prop where
  | value {v₁ v₂} : v₁ ≲ᵥ v₂ → Object.Approx (Object.value v₁) (Object.value v₂)
  | delayed {env₁ env₂ e₁ e₂} :
    e₁ ≲⟨env₁, env₂⟩ e₂ →
    Object.Approx (Object.delayed env₁ e₁) (Object.delayed env₂ e₂)

def Env.Approx : (env₁ env₂ : Env) → Prop :=
  List.Forall₂ Object.Approx

notation:40 v:40 " ≲ₒ " v':40 => Object.Approx v v'

notation:40 env₁:40 " ≲ₑ " env₂:40 => Env.Approx env₁ env₂

def Expr.Approx (e₁ e₂ : Expr) : Prop :=
  ∀ env₁ env₂, env₁ ≲ₑ env₂ → e₁ ≲⟨env₁, env₂⟩ e₂

notation:40 e₁:40 " ≲ " e₂:40 => Expr.Approx e₁ e₂

@[refl]
lemma Value.Approx.refl v : v ≲ᵥ v := by
  intro n
  rfl

@[simp]
lemma Value.Approx.unit_left {v} : v ≲ᵥ Value.unit ↔ v = Value.unit := by
  constructor
  case mp =>
    intro h
    invert (h 0)
    rfl
  case mpr =>
    intro h
    subst h
    rfl

@[simp]
lemma Value.Approx.unit_right {v} : Value.unit ≲ᵥ v ↔ v = Value.unit := by
  constructor
  case mp =>
    intro h
    invert (h 0)
    rfl
  case mpr =>
    intro h
    subst h
    rfl

@[simp]
lemma Value.Approx.const_left {v c} : v ≲ᵥ Value.const c ↔ v = Value.const c := by
  constructor
  case mp =>
    intro h
    invert (h 0)
    rfl
  case mpr =>
    intro h
    subst h
    rfl

@[simp]
lemma Value.Approx.const_right {v c} : Value.const c ≲ᵥ v ↔ v = Value.const c := by
  constructor
  case mp =>
    intro h
    invert (h 0)
    rfl
  case mpr =>
    intro h
    subst h
    rfl

@[aesop unsafe apply]
lemma Value.Approx.constr_app {ctr_name args_rev args_rev'} :
  args_rev ≲ₐ args_rev' →
  Value.constr_app ctr_name args_rev ≲ᵥ Value.constr_app ctr_name args_rev' := by
  intro h n
  apply Value.Approx.Indexed.constr_app
  intro k hk
  rw [List.forall₂_iff_zip] at *
  aesop

@[aesop safe destruct]
lemma Value.Approx.constr_app_inv {ctr_name args_rev args_rev'} :
  Value.constr_app ctr_name args_rev ≲ᵥ Value.constr_app ctr_name args_rev' →
  args_rev ≲ₐ args_rev' := by
  rw [List.forall₂_iff_zip]
  intro h
  constructor
  case left =>
    invert (h 1)
    case constr_app hargs =>
      specialize (hargs 0 _)
      · linarith
      · exact List.Forall₂.length_eq hargs
  case right =>
    intros v₁ v₂ hv n
    invert (h (n + 1))
    case constr_app hargs =>
      specialize (hargs n _)
      · linarith
      · rw [List.forall₂_iff_zip] at hargs
        aesop

lemma Value.Approx.constr_app_inv_length {ctr_name args_rev args_rev'} :
  Value.constr_app ctr_name args_rev ≲ᵥ Value.constr_app ctr_name args_rev' →
  args_rev.length = args_rev'.length := by
  intro h
  have := Value.Approx.constr_app_inv h
  exact List.Forall₂.length_eq this

@[aesop unsafe 90% destruct]
lemma Value.Approx.constr_app_inv_left {ctr_name args_rev' v} :
  v ≲ᵥ Value.constr_app ctr_name args_rev' →
  ∃ args_rev,
    v = Value.constr_app ctr_name args_rev ∧
    args_rev ≲ₐ args_rev' := by
  intro h
  invert (h 0)
  aesop

@[aesop unsafe 90% destruct]
lemma Value.Approx.constr_app_inv_right {ctr_name args_rev v} :
  Value.constr_app ctr_name args_rev ≲ᵥ v →
  ∃ args_rev',
    v = Value.constr_app ctr_name args_rev' ∧
    args_rev ≲ₐ args_rev' := by
  intro h
  invert (h 0)
  aesop

@[aesop safe destruct (immediate := [h])]
lemma Value.Approx.closure_inv {env₁ body₁ env₂ body₂}
  (h : Value.closure env₁ body₁ ≲ᵥ Value.closure env₂ body₂) :
  ∀ a₁ a₂, a₁ ≲ᵥ a₂ → body₁ ≲⟨a₁ ∷ env₁, a₂ ∷ env₂⟩ body₂ := by
  intro a₁ a₂ ha v₁ h'
  suffices ∀ n, ∃ v₂, (a₂ ∷ env₂) ⊢ body₂ ↦ v₂ ∧ v₁ ≲ᵥ(n) v₂ by
    obtain ⟨v₂, _, _⟩ := this 0
    exists v₂
    constructor
    · assumption
    · intro n
      obtain ⟨v₂', _, _⟩ := this n
      have : v₂ = v₂' := by
        apply Eval.deterministic <;> assumption
      subst this
      simp_all only
  intro n₂
  obtain ⟨n₁, h''⟩ := Eval.toIndexed h'
  invert (h (n₁ + n₂ + 1))
  case closure ch =>
    apply ch (n₁ := n₁) (n₂ := n₂)
    · linarith
    · apply ha
    · assumption

@[aesop unsafe 90% destruct]
lemma Value.Approx.closure_inv_left {env₂ body₂ v} :
  v ≲ᵥ Value.closure env₂ body₂ →
  ∃ env₁ body₁,
    v = Value.closure env₁ body₁ ∧
    (∀ a₁ a₂, a₁ ≲ᵥ a₂ → body₁ ≲⟨a₁ ∷ env₁, a₂ ∷ env₂⟩ body₂) := by
  intro h
  invert (h 0)
  aesop

@[aesop unsafe 90% destruct]
lemma Value.Approx.closure_inv_right {env₁ body₁ v} :
  Value.closure env₁ body₁ ≲ᵥ v →
  ∃ env₂ body₂,
    v = Value.closure env₂ body₂ ∧
    (∀ a₁ a₂, a₁ ≲ᵥ a₂ → body₁ ≲⟨a₁ ∷ env₁, a₂ ∷ env₂⟩ body₂) := by
  intro h
  invert (h 0)
  aesop

@[aesop safe cases]
inductive Value.Approx.Inversion : Value -> Value -> Prop where
  | unit : Value.Approx.Inversion Value.unit Value.unit
  | const {c} : Value.Approx.Inversion (Value.const c) (Value.const c)
  | constr_app {ctr_name args_rev args_rev'} :
    args_rev ≲ₐ args_rev' →
    Value.Approx.Inversion (Value.constr_app ctr_name args_rev) (Value.constr_app ctr_name args_rev')
  | closure {env₁ body₁ env₂ body₂} :
    (∀ a₁ a₂, a₁ ≲ᵥ a₂ → body₁ ≲⟨a₁ ∷ env₁, a₂ ∷ env₂⟩ body₂) →
    Value.Approx.Inversion (Value.closure env₁ body₁) (Value.closure env₂ body₂)

-- Use `invert h` to invert `h : v ≲ v'`.
@[aesop unsafe destruct]
lemma Value.Approx.invert {v v'} :
  v ≲ᵥ v' →
  Value.Approx.Inversion v v' := by
  intro h
  invert (h 0) <;> constructor <;> aesop

theorem Value.Approx.Indexed.args_trans_of_lt (n k : Nat) (args₁ args₂ args₃ : List Value) : (∀ m, m < n → ∀ {v₁ v₂ v₃}, v₁ ≲ᵥ(m) v₂ → v₂ ≲ᵥ v₃ → v₁ ≲ᵥ(m) v₃) → k < n → args₁ ≲ₐ(k) args₂ → args₂ ≲ₐ args₃ → args₁ ≲ₐ(k) args₃ := by
  intro ih hk h12 h23
  exact Juvix.Utils.forall₂_trans' (P := Value.Approx.Indexed k) (Q := Value.Approx)
    (R := Value.Approx.Indexed k) (fun a b c hab hbc => ih k hk hab hbc) h12 h23

theorem Value.Approx.Indexed.trans_step (n : Nat) (v₁ v₂ v₃ : Value) : (∀ m, m < n → ∀ {u₁ u₂ u₃}, u₁ ≲ᵥ(m) u₂ → u₂ ≲ᵥ u₃ → u₁ ≲ᵥ(m) u₃) → v₁ ≲ᵥ(n) v₂ → v₂ ≲ᵥ v₃ → v₁ ≲ᵥ(n) v₃ := by
  intro ih h₁₂ h₂₃
  invert h₁₂
  · exact h₂₃ n
  · exact h₂₃ n
  · rename_i ctr_name args₁ args₂ hargs
    obtain ⟨args₃, rfl, h₂₃args⟩ := Value.Approx.constr_app_inv_right h₂₃
    apply Value.Approx.Indexed.constr_app
    intro k hk
    exact Value.Approx.Indexed.args_trans_of_lt n k args₁ args₂ args₃ ih hk (hargs k hk) h₂₃args
  · rename_i env₁ body₁ env₂ body₂ hbody₁₂
    obtain ⟨env₃, body₃, rfl, hbody₂₃⟩ := Value.Approx.closure_inv_right h₂₃
    apply Value.Approx.Indexed.closure
    intro n₁ n₂ hlt a₁ a₃ r₁ ha₁₃ heval₁
    obtain ⟨r₂, heval₂, hr₁₂⟩ := hbody₁₂ n₁ n₂ hlt a₁ a₃ r₁ ha₁₃ heval₁
    obtain ⟨r₃, heval₃, hr₂₃⟩ := hbody₂₃ a₃ a₃ (by rfl) r₂ heval₂
    have hn₂ : n₂ < n := by linarith
    refine ⟨r₃, heval₃, ?_⟩
    exact ih n₂ hn₂ hr₁₂ hr₂₃

lemma Value.Approx.Indexed.trans {n v₁ v₂ v₃} : v₁ ≲ᵥ(n) v₂ → v₂ ≲ᵥ v₃ → v₁ ≲ᵥ(n) v₃ := by
  exact Nat.strong_induction_on (p := fun n => ∀ {u₁ u₂ u₃}, u₁ ≲ᵥ(n) u₂ → u₂ ≲ᵥ u₃ → u₁ ≲ᵥ(n) u₃) n
    (fun n ih u₁ u₂ u₃ h₁₂ h₂₃ =>
      Value.Approx.Indexed.trans_step n u₁ u₂ u₃ (fun m hm => ih m hm) h₁₂ h₂₃)


@[trans]
lemma Value.Approx.trans {v₁ v₂ v₃} : v₁ ≲ᵥ v₂ → v₂ ≲ᵥ v₃ → v₁ ≲ᵥ v₃ := by
  intros h₁ h₂
  intro n
  aesop (add unsafe apply Value.Approx.Indexed.trans)

@[refl]
lemma Expr.Approx.Param.refl {env} e : e ≲⟨env, env⟩ e := by
  intro v
  aesop

lemma Expr.Approx.Param.trans {env₁ env₂ env₃ e₁ e₂ e₃} :
  e₁ ≲⟨env₁, env₂⟩ e₂ → e₂ ≲⟨env₂, env₃⟩ e₃ → e₁ ≲⟨env₁, env₃⟩ e₃ := by
  intros h₁ h₂ v₁ heval₁
  obtain ⟨v₂, heval₂, happrox₂⟩ := h₁ v₁ heval₁
  obtain ⟨v₃, heval₃, happrox₃⟩ := h₂ v₂ heval₂
  exists v₃
  constructor
  · assumption
  · exact Value.Approx.trans happrox₂ happrox₃

@[refl]
lemma Object.Approx.refl {o} : o ≲ₒ o := by
  cases o
  case value v =>
    apply Object.Approx.value
    apply Value.Approx.refl
  case delayed env e =>
    apply Object.Approx.delayed
    rfl

@[trans]
lemma Object.Approx.trans {o₁ o₂ o₃} : o₁ ≲ₒ o₂ → o₂ ≲ₒ o₃ → o₁ ≲ₒ o₃ := by
  intros h₁ h₂
  cases h₁
  case value v₁ v₂ happrox =>
    cases h₂
    case value v₃ happrox' =>
      apply Object.Approx.value
      trans v₂ <;> assumption
  case delayed env₁ env₂ e₁ e₂ happrox =>
    cases h₂
    case delayed env₂' e₂' happrox' =>
      apply Object.Approx.delayed
      exact Expr.Approx.Param.trans happrox happrox'

@[refl]
lemma Env.Approx.refl {env} : env ≲ₑ env := by
  induction env
  case nil =>
    apply List.Forall₂.nil
  case cons hd tl ih =>
    apply List.Forall₂.cons
    · apply Object.Approx.refl
    · exact ih

@[trans]
lemma Env.Approx.trans {env₁ env₂ env₃} :
  env₁ ≲ₑ env₂ → env₂ ≲ₑ env₃ → env₁ ≲ₑ env₃ := by
  intro h₁ h₂
  simp [Env.Approx] at h₁ h₂ ⊢
  apply Utils.forall₂_trans
  · simp [Transitive]
    apply Object.Approx.trans
  · assumption
  · assumption

lemma Env.Approx.cons {env₁ env₂ o₁ o₂} :
  o₁ ≲ₒ o₂ → env₁ ≲ₑ env₂ → (o₁ :: env₁) ≲ₑ (o₂ :: env₂) := by
  intros h₁ h₂
  apply List.Forall₂.cons
  · assumption
  · assumption

lemma Env.Approx.cons_value {v₁ v₂ env} :
  v₁ ≲ᵥ v₂ → v₁ ∷ env ≲ₑ v₂ ∷ env := by
  intro h
  apply Env.Approx.cons
  · apply Object.Approx.value
    assumption
  · apply Env.Approx.refl

@[aesop unsafe apply]
lemma Value.Approx.closure {env₁ body₁ env₂ body₂} :
  (∀ a₁ a₂,
    a₁ ≲ᵥ a₂ →
    body₁ ≲⟨a₁ ∷ env₁, a₂ ∷ env₂⟩ body₂) →
  Value.closure env₁ body₁ ≲ᵥ Value.closure env₂ body₂ := by
  intro h n
  apply Value.Approx.Indexed.closure
  intro n₁ n₂ hn a₁ a₂ v₁ happrox heval
  have h₁ : ∃ v₁', a₂ ∷ env₁ ⊢ body₁ ↦ v₁' ∧ v₁ ≲ᵥ(n₂) v₁' := by
    apply Indexed.preserved n₂ n₁ (a₁ ∷ env₁) (a₂ ∷ env₁) body₁ v₁
    · simp [Env.Approx.Indexed']
      constructor
      · constructor
        have : n₂ + n₁ = n₁ + n₂ := by linarith
        rw [this]
        exact happrox
      · intros
        rfl
    · assumption
  obtain ⟨v₁', heval', happrox'⟩ := h₁
  obtain ⟨v₂, heval₂, happrox₂⟩ := h a₂ a₂ (by rfl) v₁' heval'
  exists v₂
  constructor
  · assumption
  · apply Value.Approx.Indexed.trans <;> assumption

lemma Object.Approx.toIndexed {o₁ o₂} : o₁ ≲ₒ o₂ → ∀ n, o₁ ≲ₒ'(n) o₂ := by
  intro h n
  induction h
  case value v₁ v₂ h =>
    apply Object.Approx.Indexed'.value
    apply h
  case delayed env₁ env₂ e₁ e₂ h =>
    apply Object.Approx.Indexed'.delayed
    intro n₁ n₂ v hlt heval
    obtain ⟨v₂, heval₂, happrox₂⟩ := h v (Eval.Indexed.toEval heval)
    exists v₂
    constructor
    · assumption
    · exact happrox₂ n₂

lemma Env.Approx.toIndexed {env₁ env₂} : env₁ ≲ₑ env₂ → ∀ n, env₁ ≲ₑ'(n) env₂ := by
  intro h n
  induction h
  case nil =>
    simp [Env.Approx.Indexed']
  case cons h₁ h₂ =>
    apply List.Forall₂.cons
    · apply Object.Approx.toIndexed
      assumption
    · exact h₂

lemma Expr.Approx.toIndexed {e₁ e₂} : e₁ ≲ e₂ → ∀ n, e₁ ≲'(n) e₂ := by
  intro h n n₁ n₂ v₁ hn env₁ env₂ happrox heval
  have happrox' : env₁ ≲ₑ'(n₂ + n₁) env₂ := by
    have : n₂ + n₁ = n₁ + n₂ := by linarith
    rw [this]
    assumption
  obtain ⟨v₁', heval₁', happrox₁'⟩ := Value.Approx.Indexed.preserved n₂ n₁ env₁ env₂ e₁ v₁ happrox' heval
  obtain ⟨v₂, heval₂, happrox₂⟩ := h env₂ env₂ (by rfl) v₁' heval₁'
  exists v₂
  constructor
  · assumption
  · apply Value.Approx.Indexed.trans happrox₁' happrox₂

theorem Value.Approx.preserved :
  ∀ env env' e v,
    env ≲ₑ env' →
    env ⊢ e ↦ v →
    ∃ v', env' ⊢ e ↦ v' ∧ v ≲ᵥ v' := by
  intro env env' e v h₁ h₂
  suffices ∀ n, ∃ v', env' ⊢ e ↦ v' ∧ v ≲ᵥ(n) v' by
    obtain ⟨v', heval', happrox'⟩ := this 0
    exists v'
    constructor
    · assumption
    · intro n
      obtain ⟨v'', heval'', happrox''⟩ := this n
      have : v' = v'' := by
        apply Eval.deterministic <;> assumption
      subst this
      exact happrox''
  intro m
  obtain ⟨n, h₂'⟩ := Eval.toIndexed h₂
  have h₁' : env ≲ₑ'(m + n) env' := by
    apply Env.Approx.toIndexed
    assumption
  obtain ⟨v', heval', happrox'⟩ := Value.Approx.Indexed.preserved (env := env) (env' := env') m n e v h₁' h₂'
  aesop

lemma Expr.Approx.Param.preserved {e e' env₁ env₂ env₃} :
  e ≲⟨env₁, env₂⟩ e' →
  env₂ ≲ₑ env₃ →
  e ≲⟨env₁, env₃⟩ e' := by
  intro h₁ h₂
  simp only [Expr.Approx.Param]
  intro v₁ heval₁
  obtain ⟨v₂, heval₂, happrox₂⟩ := h₁ v₁ heval₁
  obtain ⟨v₃, heval₃, happrox₃⟩ := Value.Approx.preserved env₂ env₃ e' v₂ h₂ heval₂
  exists v₃
  constructor
  · assumption
  · transitivity v₂ <;> assumption

@[refl]
lemma Expr.Approx.relf {e} : e ≲ e := by
  intro env₁ env₂ happrox v heval
  exact Value.Approx.preserved env₁ env₂ e v happrox heval

@[trans]
lemma Expr.Approx.trans {e₁ e₂ e₃} : e₁ ≲ e₂ → e₂ ≲ e₃ → e₁ ≲ e₃ := by
  intros h₁ h₂ env₁ env₂ happrox
  simp [Expr.Approx] at h₁ h₂
  apply Expr.Approx.Param.trans (h₁ env₁ env₂ happrox)
  apply h₂
  rfl

lemma Expr.Approx.from_preservation {e₁ e₂}
  (h : ∀ env v₁, env ⊢ e₁ ↦ v₁ → ∃ v₂, env ⊢ e₂ ↦ v₂ ∧ v₁ ≲ᵥ v₂)
  : e₁ ≲ e₂ := by
  intro env₁ env₂ happrox v₁ heval₁
  obtain ⟨v₂, heval₂, happrox'⟩ := h env₁ v₁ heval₁
  obtain ⟨v₂', heval₂', happrox''⟩ := Value.Approx.preserved env₁ env₂ e₂ v₂ happrox heval₂
  exists v₂'
  constructor
  · assumption
  · trans v₂ <;> assumption

lemma Expr.Approx.to_preservation {e₁ e₂} :
  e₁ ≲ e₂ →
  ∀ env v₁, env ⊢ e₁ ↦ v₁ → ∃ v₂, env ⊢ e₂ ↦ v₂ ∧ v₁ ≲ᵥ v₂ := by
  intro h
  intro env v₁ heval₁
  obtain ⟨v₂, heval₂, happrox⟩ := h env env (by rfl) v₁ heval₁
  exists v₂

lemma Expr.Approx.preservation {e₁ e₂} :
  e₁ ≲ e₂ ↔
  ∀ env v₁, env ⊢ e₁ ↦ v₁ → ∃ v₂, env ⊢ e₂ ↦ v₂ ∧ v₁ ≲ᵥ v₂ := by
  constructor
  · apply Expr.Approx.to_preservation
  · apply Expr.Approx.from_preservation

lemma Expr.Approx.const_left {c e env} :
  Expr.const c ≲ e →
  env ⊢ e ↦ Value.const c := by
  intro h
  rw [Expr.Approx.preservation] at h
  obtain ⟨v, heval, happrox⟩ := h env (Value.const c) (by constructor)
  invert happrox
  assumption

lemma Expr.Approx.const_right {c e env v} :
  e ≲ Expr.const c →
  env ⊢ e ↦ v →
  v = Value.const c := by
  intro happrox heval
  rw [Expr.Approx.preservation] at happrox
  obtain ⟨v', heval', happrox'⟩ := happrox env v heval
  cases heval'
  invert happrox'
  rfl

lemma Expr.Approx.const {c₁ c₂} :
  Expr.const c₁ ≲ Expr.const c₂ →
  c₁ = c₂ := by
  intro h
  rw [Expr.Approx.preservation] at h
  obtain ⟨v, heval, happrox⟩ := h [] (Value.const c₁) (by constructor)
  cases heval
  invert happrox
  rfl

lemma Expr.Approx.eval_const₁ {op a₁ a₂ i₁ i₂ i₃} :
  a₁ ≲ Expr.const (Constant.int i₁) →
  a₂ ≲ Expr.const (Constant.int i₂) →
  i₃ = eval_binop_int op i₁ i₂ →
  Expr.binop op a₁ a₂ ≲
    Expr.const (Constant.int i₃) := by
  intro h₁ h₂ h₃
  apply Expr.Approx.from_preservation
  intro env v₁ heval
  cases heval
  case binop val₁ val₂ heval₁ heval₂ =>
    have h₁' : i₁ = val₁ := by
      have := Expr.Approx.const_right h₁ heval₁
      cases this
      rfl
    have h₂' : i₂ = val₂ := by
      have := Expr.Approx.const_right h₂ heval₂
      cases this
      rfl
    exists Value.const (Constant.int (eval_binop_int op i₁ i₂))
    cases op <;> simp [eval_binop_int] at * <;> constructor <;>
      subst i₃ <;> first | constructor | cc

lemma Expr.Approx.eval_const₂ {op a₁ a₂ i₁ i₂ i₃} :
  Expr.const (Constant.int i₁) ≲ a₁ →
  Expr.const (Constant.int i₂) ≲ a₂ →
  i₃ = eval_binop_int op i₁ i₂ →
  Expr.const (Constant.int i₃) ≲
  Expr.binop op a₁ a₂ := by
  intro h₁ h₂ h₃
  apply Expr.Approx.from_preservation
  intro env v₁ heval
  cases heval
  case const =>
    exists Value.const (Constant.int (eval_binop_int op i₁ i₂))
    cases op <;> simp [eval_binop_int] at * <;> constructor <;> subst i₃ <;>
      constructor <;> apply Expr.Approx.const_left <;> first | rfl | assumption

end Juvix.Core.Main
