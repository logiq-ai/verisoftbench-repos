
import Mathlib.Order.Defs.Unbundled
import Aesop

namespace Juvix.Utils

theorem forall₂_trans' {α} {P Q R : α → α → Prop} {l₁ l₂ l₃}
  (h : ∀ x y z, P x y → Q y z → R x z)
  (h₁ : List.Forall₂ P l₁ l₂)
  (h₂ : List.Forall₂ Q l₂ l₃)
  : List.Forall₂ R l₁ l₃ := by
  induction h₁ generalizing l₃
  case nil =>
    cases h₂
    case nil =>
      constructor
  case cons x y xs ys h₁ h₂ ih =>
    cases h₂
    case cons y' ys' h₂' h₃ =>
      constructor
      exact h x y y' h₁ h₂'
      exact ih h₃

theorem forall₂_trans {α} {P : α → α → Prop} (h : Transitive P) : Transitive (List.Forall₂ P) := by
  intro l₁ l₂ l₃ h₁ h₂
  apply forall₂_trans' (P := P) (Q := P) (R := P)
  · exact h
  · exact h₁
  · exact h₂

end Juvix.Utils
