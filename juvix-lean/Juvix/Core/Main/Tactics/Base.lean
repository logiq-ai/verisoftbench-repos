
import Juvix.Core.Main.Semantics

namespace Juvix.Core.Main

macro "approx" : tactic => `(tactic| constructor <;> apply Expr.Approx.from_preservation)

macro "trivial" : tactic => `(tactic| (first
  | constructor
  | assumption
  | rfl))

end Juvix.Core.Main
