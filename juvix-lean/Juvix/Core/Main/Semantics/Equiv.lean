
import Juvix.Core.Main.Semantics.Approx

namespace Juvix.Core.Main

def Value.Equiv (v v' : Value) : Prop :=
  v ≲ᵥ v' ∧ v' ≲ᵥ v

notation:40 v:40 " ≈ᵥ " v':40 => Value.Equiv v v'

notation:40 args₁:40 " ≈ₐ " args₂:40 => List.Forall₂ Value.Equiv args₁ args₂

def Object.Equiv (o o' : Object) : Prop :=
  o ≲ₒ o' ∧ o' ≲ₒ o

def Env.Equiv : (env₁ env₂ : Env) → Prop :=
  List.Forall₂ Object.Equiv

notation:40 v:40 " ≈ₒ " v':40 => Object.Equiv v v'

notation:40 env₁:40 " ≈ₑ " env₂:40 => Env.Equiv env₁ env₂

def Expr.Equiv.Param (env₁ env₂ : Env) (e₁ e₂ : Expr) : Prop :=
  e₁ ≲⟨env₁, env₂⟩ e₂ ∧ e₂ ≲⟨env₂, env₁⟩ e₁

notation:40 e₁:40 " ≈⟨" env₁:40 ", " env₂:40 "⟩ " e₂:40 => Expr.Equiv.Param env₁ env₂ e₁ e₂

def Expr.Equiv (e₁ e₂ : Expr) : Prop :=
  e₁ ≲ e₂ ∧ e₂ ≲ e₁

notation:40 e₁:40 " ≈ " e₂:40 => Expr.Equiv e₁ e₂

lemma Value.Equiv.toApprox₁ {v₁ v₂} : v₁ ≈ᵥ v₂ → v₁ ≲ᵥ v₂ := by
  simp_all only [Value.Equiv]
  simp

lemma Value.Equiv.toApprox₂ {v₁ v₂} : v₁ ≈ᵥ v₂ → v₂ ≲ᵥ v₁ := by
  simp_all only [Value.Equiv]
  simp

lemma Value.Approx.toEquiv {v₁ v₂} : v₁ ≲ᵥ v₂ → v₂ ≲ᵥ v₁ → v₁ ≈ᵥ v₂ := by
  simp_all only [Value.Equiv]
  simp

@[refl]
lemma Value.Equiv.refl {v} : v ≈ᵥ v := by
  simp [Value.Equiv]
  rfl

@[symm]
lemma Value.Equiv.symm {v₁ v₂} : v₁ ≈ᵥ v₂ → v₂ ≈ᵥ v₁ := by
  intro h
  simp_all only [Value.Equiv]
  simp

@[trans]
lemma Value.Equiv.trans {v₁ v₂ v₃} : v₁ ≈ᵥ v₂ → v₂ ≈ᵥ v₃ → v₁ ≈ᵥ v₃ := by
  intros h₁ h₂
  simp_all only [Value.Equiv]
  aesop (add unsafe Value.Approx.trans)

lemma Object.Equiv.toApprox {o₁ o₂} : o₁ ≈ₒ o₂ → o₁ ≲ₒ o₂ := by
  simp_all only [Object.Equiv]
  simp

lemma Object.Equiv.toApprox' {o₁ o₂} : o₁ ≈ₒ o₂ → o₂ ≲ₒ o₁ := by
  simp_all only [Object.Equiv]
  simp

lemma Object.Approx.toEquiv {o₁ o₂} : o₁ ≲ₒ o₂ → o₂ ≲ₒ o₁ → o₁ ≈ₒ o₂ := by
  simp_all only [Object.Equiv]
  simp

@[refl]
lemma Object.Equiv.refl {o} : o ≈ₒ o := by
  simp [Object.Equiv]
  rfl

@[symm]
lemma Object.Equiv.symm {o₁ o₂} : o₁ ≈ₒ o₂ → o₂ ≈ₒ o₁ := by
  intro h
  simp_all only [Object.Equiv]
  simp

@[trans]
lemma Object.Equiv.trans {o₁ o₂ o₃} : o₁ ≈ₒ o₂ → o₂ ≈ₒ o₃ → o₁ ≈ₒ o₃ := by
  intros h₁ h₂
  simp_all only [Object.Equiv]
  aesop (add unsafe Object.Approx.trans)

lemma Env.Equiv.toApprox₁ {env₁ env₂} : env₁ ≈ₑ env₂ → env₁ ≲ₑ env₂ := by
  intro h
  simp [Env.Equiv] at h
  apply List.Forall₂.imp @Object.Equiv.toApprox
  assumption

lemma Env.Equiv.toApprox₂ {env₁ env₂} : env₁ ≈ₑ env₂ → env₂ ≲ₑ env₁ := by
  intro h
  simp [Env.Equiv] at h
  apply List.Forall₂.flip
  apply List.Forall₂.imp @Object.Equiv.toApprox' h

lemma Env.Equiv.toApprox {env₁ env₂} : env₁ ≈ₑ env₂ → env₁ ≲ₑ env₂ ∧ env₂ ≲ₑ env₁ := by
    intro h
    exact ⟨Env.Equiv.toApprox₁ h, Env.Equiv.toApprox₂ h⟩

lemma Env.Approx.toEquiv {env₁ env₂} : env₁ ≲ₑ env₂ → env₂ ≲ₑ env₁ → env₁ ≈ₑ env₂ := by
  intro h₁ h₂
  simp [Env.Equiv]
  simp_all [Env.Approx]
  have h₂' := List.Forall₂.flip h₂
  apply List.Forall₂.mp
  · apply Object.Approx.toEquiv
  · assumption
  · assumption


@[refl]
lemma Env.Equiv.refl {env} : env ≈ₑ env := by
  simp [Env.Equiv]
  intros
  rfl

@[symm]
lemma Env.Equiv.symm {env₁ env₂} : env₁ ≈ₑ env₂ → env₂ ≈ₑ env₁ := by
  intro h
  apply Env.Approx.toEquiv
  · apply Env.Equiv.toApprox₂ h
  · apply Env.Equiv.toApprox₁ h

@[trans]
lemma Env.Equiv.trans {env₁ env₂ env₃} : env₁ ≈ₑ env₂ → env₂ ≈ₑ env₃ → env₁ ≈ₑ env₃ := by
  intros h₁ h₂
  apply Env.Approx.toEquiv
  · have := Env.Equiv.toApprox₁ h₁
    have := Env.Equiv.toApprox₁ h₂
    aesop (add unsafe Env.Approx.trans)
  · have := Env.Equiv.toApprox₂ h₁
    have := Env.Equiv.toApprox₂ h₂
    aesop (add unsafe Env.Approx.trans)

lemma Expr.Equiv.toParam {e₁ e₂ env₁ env₂} : e₁ ≈ e₂ → env₁ ≈ₑ env₂ → e₁ ≈⟨env₁, env₂⟩ e₂ := by
  intro hequiv henv
  simp [Expr.Equiv.Param]
  simp [Expr.Equiv] at hequiv
  rcases hequiv with ⟨h₁, h₂⟩
  simp [Expr.Approx] at h₁ h₂
  have := h₁ env₁ env₂ (Env.Equiv.toApprox₁ henv)
  have := h₂ env₂ env₁ (Env.Equiv.toApprox₂ henv)
  simp_all only [and_self]

lemma Expr.Equiv.fromParam {e₁ e₂} : (∀ env₁ env₂, env₁ ≈ₑ env₂ → e₁ ≈⟨env₁, env₂⟩ e₂) → e₁ ≈ e₂ := by
  intro h
  simp [Expr.Equiv]
  constructor
  · apply Expr.Approx.from_preservation
    intro env v₁ heval
    obtain ⟨h₁, h₂⟩ := h env env (by rfl)
    simp [Expr.Approx.Param] at h₁
    exact h₁ v₁ heval
  · apply Expr.Approx.from_preservation
    intro env v₁ heval
    obtain ⟨h₁, h₂⟩ := h env env (by rfl)
    simp [Expr.Approx.Param] at h₂
    exact h₂ v₁ heval

lemma Expr.Equiv.toApprox₁ {e₁ e₂} : e₁ ≈ e₂ → e₁ ≲ e₂ := by
  simp [Expr.Equiv]
  simp_all only [implies_true]

lemma Expr.Equiv.toApprox₂ {e₁ e₂} : e₁ ≈ e₂ → e₂ ≲ e₁ := by
  simp [Expr.Equiv]

lemma Expr.Equiv.toApprox {e₁ e₂} : e₁ ≈ e₂ → e₁ ≲ e₂ ∧ e₂ ≲ e₁ := by
    intro h
    exact ⟨Expr.Equiv.toApprox₁ h, Expr.Equiv.toApprox₂ h⟩

lemma Expr.Approx.toEquiv {e₁ e₂} : e₁ ≲ e₂ → e₂ ≲ e₁ → e₁ ≈ e₂ := by
  simp [Expr.Equiv]
  simp_all only [and_self, implies_true]

lemma Expr.Equiv.Approx.equiv {e₁ e₂} : e₁ ≈ e₂ ↔ e₁ ≲ e₂ ∧ e₂ ≲ e₁ := by
  constructor
  case mp =>
    apply Expr.Equiv.toApprox
  case mpr =>
    aesop (add unsafe Expr.Approx.toEquiv)

@[refl]
lemma Expr.Equiv.refl {e} : e ≈ e := by
  simp [Expr.Equiv]
  rfl

@[trans]
lemma Expr.Equiv.trans {e₁ e₂ e₃} : e₁ ≈ e₂ → e₂ ≈ e₃ → e₁ ≈ e₃ := by
  simp [Expr.Equiv]
  aesop (add unsafe Expr.Approx.trans)

@[symm]
lemma Expr.Equiv.symm {e₁ e₂} : e₁ ≈ e₂ → e₂ ≈ e₁ := by
  intro
  simp_all only [Equiv.Approx.equiv, and_self]

lemma Expr.Equiv.const {c₁ c₂} :
  Expr.const c₁ ≈ Expr.const c₂ →
  c₁ = c₂ := by
  intro ⟨h₁, h₂⟩
  apply Expr.Approx.const
  assumption

lemma Expr.Equiv.eval_const {op a₁ a₂ i₁ i₂ i₃} :
  a₁ ≈ Expr.const (Constant.int i₁) →
  a₂ ≈ Expr.const (Constant.int i₂) →
  i₃ = eval_binop_int op i₁ i₂ →
  Expr.binop op a₁ a₂ ≈
    Expr.const (Constant.int i₃) := by
  simp only [Expr.Equiv]
  intro h₁ h₂ h₃
  constructor
  · apply Expr.Approx.eval_const₁ (op := op) (i₁ := i₁) (i₂ := i₂) <;>
      simp_all only
  · apply Expr.Approx.eval_const₂ (op := op) (i₁ := i₁) (i₂ := i₂) <;>
      simp_all only

end Juvix.Core.Main
