
import Juvix.Core.Main.Language

namespace Juvix.Core.Main.Syntax.Test

example : ⟪1⟫ = Expr.const (Constant.int 1) := by
  rfl

example : ⟪"hello"⟫ = Expr.const (Constant.string "hello") := by
  rfl

example : ⟪x♯0⟫ = Expr.var "x" 0 := by
  rfl

example : ⟪λx . λx x♯0 x♯0⟫ = Expr.lambda "x" (Expr.lambda "x" (Expr.var "x" 0) @@ Expr.var "x" 0) := by
  rfl

example : ⟪λx . x♯0 x♯0⟫ = Expr.lambda "x" (Expr.var "x" 0 @@ Expr.var "x" 0) := by
  rfl

example : ⟪λx y . x♯1 y♯0⟫ = Expr.lambda "x" (Expr.lambda "y" (Expr.var "x" 1 @@ Expr.var "y" 0)) := by
  rfl

example : ⟪λx y z . x♯2 z♯0 (y♯1 z♯0)⟫ = Expr.lambda "x"
  (Expr.lambda "y" (Expr.lambda "z" (Expr.var "x" 2 @@ Expr.var "z" 0 @@ (Expr.var "y" 1 @@ Expr.var "z" 0)))) := by
  rfl

example : ⟪λx . x♯0 + 1⟫ = Expr.lambda "x" (Expr.binop BinaryOp.add_int (Expr.var "x" 0) (Expr.const (Constant.int 1))) := by
  rfl

example : ⟪true⟫ = Expr.constr "true" := by
  rfl

example : ⟪cons υ 1 nil⟫ = (((Expr.constr "cons").constr_app Expr.unit).constr_app (Expr.const (Constant.int 1))).constr_app
  (Expr.constr "nil") := by
  rfl

example : ⟪cons 1 (cons 2 nil)⟫ =
  ((Expr.constr "cons").constr_app (Expr.const (Constant.int 1))).constr_app
    (((Expr.constr "cons").constr_app (Expr.const (Constant.int 2))).constr_app
      (Expr.constr "nil"))  := by
  rfl

example : ⟪cons 1 (cons 2 (cons 3 nil))⟫ = ((Expr.constr "cons").constr_app (Expr.const (Constant.int 1))).constr_app
  (((Expr.constr "cons").constr_app (Expr.const (Constant.int 2))).constr_app
    (((Expr.constr "cons").constr_app (Expr.const (Constant.int 3))).constr_app (Expr.constr "nil"))) := by
  rfl

example : ⟪1 + let x := 7 in x♯0 + 3⟫ = Expr.binop BinaryOp.add_int
  (Expr.const (Constant.int 1))
  (Expr.save "x" (Expr.const (Constant.int 7))
    (Expr.binop BinaryOp.add_int (Expr.var "x" 0)
      (Expr.const (Constant.int 3)))) := by
  rfl

example : ⟪let id := λx . x♯0 + 1 in id♯0⟫ = Expr.save "id"
  (Expr.lambda "x"
    (Expr.binop BinaryOp.add_int (Expr.var "x" 0)
      (Expr.const (Constant.int 1))))
  (Expr.var "id" 0) := by
  rfl

example : ⟪letrec f := λx . x♯0 + f♯1 x♯0 in f♯0 1⟫ = Expr.save "f"
  (Expr.recur "f"
    (Expr.lambda "x"
      (Expr.binop BinaryOp.add_int (Expr.var "x" 0)
        (Expr.var "f" 1 @@ Expr.var "x" 0))))
  (Expr.var "f" 0 @@ Expr.const (Constant.int 1)) := by
  rfl

example : ⟪rec f λ x . x♯0 + f♯1 x♯0⟫ = Expr.recur "f"
  (Expr.lambda "x"
    (Expr.binop BinaryOp.add_int (Expr.var "x" 0)
      (Expr.var "f" 1 @@ Expr.var "x" 0))) := by
  rfl

example : ⟪case cons 1 nil of | cons x xs => cons (x♯1 + 1) xs♯0 | _ => nil end⟫ =
  Expr.save "_case_"
    (((Expr.constr "cons").constr_app
          (Expr.const (Constant.int 1))).constr_app
      (Expr.constr "nil"))
    (Expr.branch "cons" ["x", "xs"]
      (((Expr.constr "cons").constr_app
            (Expr.binop BinaryOp.add_int (Expr.var "x" 1)
              (Expr.const (Constant.int 1)))).constr_app
        (Expr.var "xs" 0))
      (Expr.constr "nil")) := by
  rfl

example : ⟪case cons 1 nil of | cons x xs => cons (x♯1 + 1) xs♯0 | nil => nil | _ => ⊥ end⟫ =
  Expr.save "_case_"
    (((Expr.constr "cons").constr_app
          (Expr.const (Constant.int 1))).constr_app
      (Expr.constr "nil"))
    (Expr.branch "cons" ["x", "xs"]
      (((Expr.constr "cons").constr_app
            (Expr.binop BinaryOp.add_int (Expr.var "x" 1)
              (Expr.const (Constant.int 1)))).constr_app
        (Expr.var "xs" 0))
      (Expr.branch "nil" [] (Expr.constr "nil")
        Expr.fail)) := by
  rfl

example : ⟪case cons 1 nil of | cons x xs => cons (x♯1 + 1) xs♯0 | nil => nil end⟫ =
  Expr.save "_case_"
    (((Expr.constr "cons").constr_app
          (Expr.const (Constant.int 1))).constr_app
      (Expr.constr "nil"))
    (Expr.branch "cons" ["x", "xs"]
      (((Expr.constr "cons").constr_app
            (Expr.binop BinaryOp.add_int (Expr.var "x" 1)
              (Expr.const (Constant.int 1)))).constr_app
        (Expr.var "xs" 0))
      (Expr.branch "nil" [] (Expr.constr "nil")
        Expr.fail)) := by
  rfl

example : ⟪⊥⟫ = Expr.fail := by
  rfl

end Juvix.Core.Main.Syntax.Test
