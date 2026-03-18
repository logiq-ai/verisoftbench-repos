
import Juvix.Core.Main.Language.Base

namespace Juvix.Core.Main.Syntax

open Lean hiding Expr

declare_syntax_cat expr
declare_syntax_cat cases

syntax num : expr
syntax str : expr
syntax (name := expr_var) ident "♯" num : expr
syntax "υ" : expr
syntax:100 expr:100 ppSpace expr:101 : expr
syntax ident : expr
syntax:100 (name := expr_constr_app) ident (ppSpace expr:110)+ : expr
syntax:50 expr:50 " + " expr:51 : expr
syntax:50 expr:50 " - " expr:50 : expr
syntax:60 expr:60 " * " expr:61 : expr
syntax:60 expr:60 " / " expr:60 : expr
syntax "λ" ident expr:110 : expr
syntax "λ " ident+ " . " expr:40 : expr
syntax "let " ident " := " expr " in " expr : expr
syntax "letrec " ident " := " expr " in " expr : expr
syntax "rec " ident ppSpace expr : expr
syntax "case " expr " of " cases " end" : expr
syntax "⊥" : expr
syntax:110 "(" expr ")" : expr

syntax "| " ident " => " expr ppSpace cases+ : cases
syntax (name := cases_multiple) "| " ident (ppSpace ident)+ " => " expr ppSpace cases+ : cases
syntax (name := cases_single_simple)  "| " ident " => " expr : cases
syntax (name := cases_single) "| " ident (ppSpace ident)+ " => " expr : cases
syntax "| " "_" " => " expr : cases

syntax (name := term_of_cases) "⟪cases|" cases "⟫" : term
syntax (name := term_of_expr) "⟪" expr "⟫" : term

def mkLambdas {m} [Monad m] [MonadQuotation m] (ss : TSyntaxArray `ident) (e : TSyntax `expr) : m (TSyntax `term) := do
  let body ← `(⟪ $e ⟫)
  ss.foldrM (fun s acc => `(Expr.lambda $(Lean.Syntax.mkStrLit s.getId.toString) $acc)) body

def mkConstrApp {m} [Monad m] [MonadQuotation m] (s : TSyntax `ident) (es : TSyntaxArray `expr) : m (TSyntax `term) := do
  let ctr ← `(Expr.constr $(Lean.Syntax.mkStrLit s.getId.toString))
  es.foldlM (fun acc e => `(Expr.constr_app $acc ⟪$e⟫)) ctr

macro_rules
  | `(⟪$s:ident ♯ $i:num⟫) => `(Expr.var $(Lean.Syntax.mkStrLit s.getId.toString) $i)
  | `(⟪$num:num⟫) => `(Expr.const (Constant.int $num))
  | `(⟪$s:str⟫) => `(Expr.const (Constant.string $s))
  | `(⟪υ⟫) => `(Expr.unit)
  | `(⟪$e₁:expr $e₂:expr⟫) => `(Expr.app ⟪$e₁⟫ ⟪$e₂⟫)
  | `(⟪λ $s:ident $e:expr⟫) => `(Expr.lambda $(Lean.Syntax.mkStrLit s.getId.toString) ⟪$e⟫)
  | `(⟪λ $ss:ident* . $e:expr⟫) => mkLambdas ss e
  | `(⟪ $s:ident ⟫) => `(Expr.constr $(Lean.Syntax.mkStrLit s.getId.toString))
  | `(⟪ $s:ident $es:expr* ⟫) => mkConstrApp s es
  | `(⟪$e₁ + $e₂⟫) => `(Expr.binop BinaryOp.add_int ⟪$e₁⟫ ⟪$e₂⟫)
  | `(⟪$e₁ - $e₂⟫) => `(Expr.binop BinaryOp.sub_int ⟪$e₁⟫ ⟪$e₂⟫)
  | `(⟪$e₁ * $e₂⟫) => `(Expr.binop BinaryOp.mul_int ⟪$e₁⟫ ⟪$e₂⟫)
  | `(⟪$e₁ / $e₂⟫) => `(Expr.binop BinaryOp.div_int ⟪$e₁⟫ ⟪$e₂⟫)
  | `(⟪let $s:ident := $e₁:expr in $e₂:expr⟫) => `(Expr.save $(Lean.Syntax.mkStrLit s.getId.toString) ⟪$e₁⟫ ⟪$e₂⟫)
  | `(⟪letrec $s:ident := $e₁:expr in $e₂:expr⟫) =>
    let name := Lean.Syntax.mkStrLit s.getId.toString
    `(Expr.save $name (Expr.recur $name ⟪$e₁⟫) ⟪$e₂⟫)
  | `(⟪rec $s:ident $e:expr⟫) =>
    let name := Lean.Syntax.mkStrLit s.getId.toString
    `(Expr.recur $name ⟪$e⟫)
  | `(⟪⊥⟫) => `(Expr.fail)
  | `(⟪cases| | $s:ident => $e:expr $cs:cases ⟫) =>
    let name := Lean.Syntax.mkStrLit s.getId.toString
    `(Expr.branch $name [] ⟪$e⟫ ⟪cases|$cs⟫)
  | `(⟪cases| | $s:ident $ss:ident* => $e:expr $cs:cases ⟫) =>
    let name := Lean.Syntax.mkStrLit s.getId.toString
    let vnames := ss.toList.map fun s => s.getId.toString
    `(Expr.branch $name $(quote vnames) ⟪$e⟫ ⟪cases|$cs⟫)
  | `(⟪cases| | $s:ident => $e:expr ⟫) =>
    let name := Lean.Syntax.mkStrLit s.getId.toString
    `(Expr.branch $name [] ⟪$e⟫ Expr.fail)
  | `(⟪cases| | $s:ident $ss:ident* => $e:expr ⟫) =>
    let name := Lean.Syntax.mkStrLit s.getId.toString
    let vnames := ss.toList.map fun s => s.getId.toString
    `(Expr.branch $name $(quote vnames) ⟪$e⟫ Expr.fail)
  | `(⟪cases| | _ => $e:expr ⟫) =>
    `(⟪$e⟫)
  | `(⟪case $e:expr of $cs:cases end⟫) => do
    `(Expr.save "_case_" ⟪$e⟫ ⟪cases|$cs⟫)
  | `(⟪($e)⟫) => `(⟪$e⟫)

instance : Coe Syntax (TSyntax `expr) where
  coe s := ⟨s⟩

end Juvix.Core.Main.Syntax
