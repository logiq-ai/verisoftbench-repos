
import Juvix.Core.Main.Semantics.Approx.Contextual

namespace Juvix.Core.Main

def Expr.Equiv.Contextual (e₁ e₂ : Expr) : Prop :=
  e₁ ≲ᶜ e₂ ∧ e₂ ≲ᶜ e₁

notation:40 e₁ " ≈ᶜ " e₂:40 => Expr.Equiv.Contextual e₁ e₂

end Juvix.Core.Main
