
import Juvix.Core.Main.Tactics.Congr
import Juvix.Core.Main.Tactics.Termination

namespace Juvix.Core.Main

macro "prove_inlining" : tactic => `(tactic| (first
  | rfl
  | (apply Expr.Equiv.fromParam; congr_equiv <;> prove_termination)))

end Juvix.Core.Main
