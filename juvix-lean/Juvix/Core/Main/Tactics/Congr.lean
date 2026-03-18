
import Juvix.Core.Main.Tactics.Termination

namespace Juvix.Core.Main

macro "congr_approx_only" : tactic => `(tactic| (first
  | apply Expr.Approx.cong_app
  | apply Expr.Approx.cong_constr_app
  | apply Expr.Approx.cong_binop
  | apply Expr.Approx.cong_lambda
  | apply Expr.Approx.cong_save
  | apply Expr.Approx.cong_branch
  | apply Expr.Approx.cong_recur))

macro "congr_approx_param_only" : tactic => `(tactic| (first
  | apply Expr.Approx.Param.cong_app
  | apply Expr.Approx.Param.cong_unit
  | apply Expr.Approx.Param.cong_const
  | apply Expr.Approx.Param.cong_constr
  | apply Expr.Approx.Param.cong_constr_app
  | apply Expr.Approx.Param.cong_binop
  | apply Expr.Approx.Param.cong_lambda
  | apply Expr.Approx.Param.cong_save
  | apply Expr.Approx.Param.cong_branch
  | apply Expr.Approx.Param.cong_recur
  | apply Expr.Approx.Param.cong_fail))

macro "congr_approx_step" : tactic => `(tactic| (first
  | intro _
  | rfl
  | assumption
  | congr_approx_only
  | congr_approx_param_only))

macro "congr_approx" : tactic => `(tactic| repeat' congr_approx_step)

macro "congr_equiv_only" : tactic => `(tactic| (first
  | apply Expr.Equiv.cong_app
  | apply Expr.Equiv.cong_constr_app
  | apply Expr.Equiv.cong_binop
  | apply Expr.Equiv.cong_lambda
  | apply Expr.Equiv.cong_save
  | apply Expr.Equiv.cong_branch
  | apply Expr.Equiv.cong_recur))

macro "congr_equiv_param_only" : tactic => `(tactic| (first
  | apply Expr.Equiv.Param.cong_var
  | apply Expr.Equiv.Param.cong_unit
  | apply Expr.Equiv.Param.cong_const
  | apply Expr.Equiv.Param.cong_constr
  | apply Expr.Equiv.Param.cong_app
  | apply Expr.Equiv.Param.cong_constr_app
  | apply Expr.Equiv.Param.cong_binop
  | apply Expr.Equiv.Param.cong_lambda
  | apply Expr.Equiv.Param.cong_save
  | apply Expr.Equiv.Param.cong_branch
  | apply Expr.Equiv.Param.cong_recur
  | apply Expr.Equiv.Param.cong_fail))

macro "congr_equiv_step" : tactic => `(tactic| (first
  | intro _
  | rfl
  | assumption
  | congr_equiv_only
  | congr_equiv_param_only))

macro "congr_equiv" : tactic => `(tactic| repeat' congr_equiv_step)

macro "congr_step" : tactic => `(tactic| (first
  | intro _
  | rfl
  | assumption
  | congr_equiv_param_only
  | congr_equiv_only
  | congr_approx_param_only
  | congr_approx_only))

macro "congr" : tactic => `(tactic| repeat' congr_step)

end Juvix.Core.Main
