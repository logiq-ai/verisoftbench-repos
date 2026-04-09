
import Juvix.Core.Main.Tactics.Base

namespace Juvix.Core.Main

macro "eval_const_step" : tactic => `(tactic| first
  | apply Expr.Equiv.eval_const
  | apply Expr.Equiv.symm; apply Expr.Equiv.eval_const
  | rfl)

macro "eval_const" : tactic => `(tactic| repeat' eval_const_step)

end Juvix.Core.Main
