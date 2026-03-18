
import Juvix.Core.Main.Tactics.Congr
import Juvix.Core.Main.Tactics.Eval

namespace Juvix.Core.Main

macro "prove_constant_folding" : tactic => `(tactic|
  (congr_equiv <;> eval_const))

end Juvix.Core.Main
