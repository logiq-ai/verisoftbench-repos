
import Juvix.Core.Main.Language
import Juvix.Core.Main.Language.Context
import Juvix.Core.Main.Semantics.Eval

namespace Juvix.Core.Main

def Expr.Approx.Contextual (e₁ e₂ : Expr) : Prop :=
  ∀ (C : Context) env, env ⊢ C.subst e₁ ↓ → env ⊢ C.subst e₂ ↓

notation:40 e₁ " ≲ᶜ " e₂:40 => Expr.Approx.Contextual e₁ e₂

end Juvix.Core.Main
