
import Juvix.Core.Main.Language.Syntax

namespace Juvix.Core.Main.Pretty

open Lean hiding Expr
open PrettyPrinter Delaborator SubExpr Parenthesizer

def mkVar {m} [Monad m] [MonadRef m] (name : Ident) (i : TSyntax `num) : m Syntax := do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  pure $
      Lean.Syntax.node3 info `Juvix.Core.Main.Syntax.term_of_expr
            (Lean.Syntax.atom info "⟪")
            (Lean.Syntax.node3 info `Juvix.Core.Main.Syntax.expr_var
              name (Lean.Syntax.atom info "♯") i)
            (Lean.Syntax.atom info "⟫")

def mkConstrApp {m} [Monad m] [MonadRef m] (name : Ident) (es : TSyntaxArray `expr) : m Syntax := do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  pure $
    Lean.Syntax.node3 info `Juvix.Core.Main.Syntax.term_of_expr
      (Lean.Syntax.atom info "⟪")
      (Lean.Syntax.node2 info `Juvix.Core.Main.Syntax.expr_constr_app
        name
        (Lean.Syntax.node info `null es))
      (Lean.Syntax.atom info "⟫")

def unfoldListLit (node : Syntax) : Option (List String) :=
  match node with
  | (Lean.Syntax.node _ _ args0) =>
    match args0 with
    | #[Lean.Syntax.atom _ "[", node', Lean.Syntax.atom _ "]"] =>
      match node' with
      | (Lean.Syntax.node _ _ args) =>
        let rec go : List Syntax → List String → Option (List String)
          | [], acc => some acc.reverse
          | [ ns ], acc =>
            match ns with
            | `($s:str) =>
              some (s.getString :: acc).reverse
            | _ => none
          | ( ns :: Lean.Syntax.atom _ "," :: xs), acc =>
            match ns with
            | `($s:str) =>
                go xs (s.getString :: acc)
            | _ => none
          | _, _ => none
        go args.toList []
      | _ => none
    | _ => none
  | _ => none

@[app_unexpander Expr.var]
def unexpandVar : Unexpander
  | `($_var $s:str $i:num) =>
    let name := mkIdent $ Name.mkSimple s.getString
    mkVar name i
  | _ => throw ()

@[app_unexpander Expr.unit]
def unexpandUnit : Unexpander
  | `($_unit) => `(⟪υ⟫)

@[app_unexpander Expr.const]
def unexpandConst : Unexpander
  | `($_const $x) =>
    match x with
    | `($_ $n:num) => `(⟪$n⟫)
    | `($_ $s:str) => `(⟪$s⟫)
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Expr.app]
def unexpandApp : Unexpander
  | `($_app ⟪$e₁⟫ ⟪$e₂⟫) => `(⟪$e₁ $e₂⟫)
  | _ => throw ()

@[app_unexpander Expr.constr]
def unexpandConstr : Unexpander
  | `($_constr $s:str) =>
    let name := mkIdent $ Name.mkSimple s.getString
    `(⟪ $name ⟫)
  | _ => throw ()

@[app_unexpander Expr.constr_app]
def unexpandConstrApp : Unexpander
  | `($_constr_app ⟪ $s ⟫ ⟪$e⟫) => `(⟪ $s $e⟫)
  | `($_constr_app ⟪ $s:ident $es* ⟫ ⟪$e⟫) => mkConstrApp s (es.push e)
  | _ => throw ()

@[app_unexpander Expr.lambda]
def unexpandLambda : Unexpander
  | `($_lambda $s:str ⟪λ $ss:ident* . $e:expr⟫) =>
    let name := mkIdent $ Name.mkSimple s.getString
    `(⟪λ $name $ss* . $e⟫)
  | `($_lambda $s:str ⟪$e⟫) =>
    let name := mkIdent $ Name.mkSimple s.getString
    `(⟪λ $name . $e⟫)
  | _ => throw ()

@[delab app.Juvix.Core.Main.Expr.binop]
def delabBinop : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' `Juvix.Core.Main.Expr.binop 3
  match e.getAppArgs' with
  | #[Lean.Expr.const op _, e₁, e₂] =>
    let e₁' ← match ← delab e₁ with
      | `(⟪$e'⟫) => pure e'
      | _ => failure
    let e₂' ← match ← delab e₂ with
      | `(⟪$e'⟫) => pure e'
      | _ => failure
    match op with
    | `Juvix.Core.Main.BinaryOp.add_int => `(⟪$e₁' + $e₂'⟫)
    | `Juvix.Core.Main.BinaryOp.sub_int => `(⟪$e₁' - $e₂'⟫)
    | `Juvix.Core.Main.BinaryOp.mul_int => `(⟪$e₁' * $e₂'⟫)
    | `Juvix.Core.Main.BinaryOp.div_int => `(⟪$e₁' / $e₂'⟫)
    | _ => failure
  | _ => failure

@[app_unexpander Expr.branch]
def unexpandBranch : Unexpander
  | `($_branch $s:str $lst ⟪$body:expr⟫ ⟪cases| $c:cases⟫) =>
    let name := mkIdent $ Name.mkSimple s.getString
    match unfoldListLit lst with
    | some ss =>
      let names := List.toArray $ ss.map fun s' => mkIdent (Name.mkSimple s')
      if ss.isEmpty then
        `(⟪cases| | $name => $body $c⟫)
      else
        `(⟪cases| | $name $names* => $body $c⟫)
    | none =>
      throw ()
  | `($_branch $s:str $lst ⟪$body:expr⟫ ⟪⊥⟫) =>
    let name := mkIdent $ Name.mkSimple s.getString
    match unfoldListLit lst with
    | some ss =>
      let names := List.toArray $ ss.map fun s' => mkIdent (Name.mkSimple s')
      if ss.isEmpty then
        `(⟪cases| | $name => $body⟫)
      else
        `(⟪cases| | $name $names* => $body⟫)
    | none =>
      throw ()
  | `($_branch $s:str $lst ⟪$body:expr⟫ ⟪$next:expr⟫) =>
    let name := mkIdent $ Name.mkSimple s.getString
    match unfoldListLit lst with
    | some ss =>
      let names := List.toArray $ ss.map fun s' => mkIdent (Name.mkSimple s')
      if ss.isEmpty then
        `(⟪cases| | $name => $body | _ => $next⟫)
      else
        `(⟪cases| | $name $names* => $body | _ => $next⟫)
    | none =>
      throw ()
  | _ => throw ()

@[app_unexpander Expr.save]
def unexpandSave : Unexpander
  | `($_save "_case_" ⟪$v:expr⟫ ⟪cases| $c⟫) =>
    `(⟪case $v of $c end⟫)
  | `($_save $s:str ⟪rec $sname:ident $v:expr⟫ ⟪$b:expr⟫) =>
    if sname.getId.toString == s.getString then
      `(⟪letrec $sname := $v in $b⟫)
    else
      throw ()
  | `($_save $s:str ⟪$v:expr⟫ ⟪$b:expr⟫) =>
    let name := mkIdent $ Name.mkSimple s.getString
    `(⟪let $name := $v in $b⟫)
  | _ => throw ()

@[app_unexpander Expr.recur]
def unexpandRecur : Unexpander
  | `($_recur $s:str ⟪$b:expr⟫) =>
    let name := mkIdent $ Name.mkSimple s.getString
    `(⟪rec $name $b⟫)
  | _ => throw ()

@[app_unexpander Expr.fail]
def unexpandFail : Unexpander
  | `($_bot) => `(⟪⊥⟫)

@[category_parenthesizer expr]
def expr.parenthesizer : CategoryParenthesizer := term.parenthesizer

end Juvix.Core.Main.Pretty
