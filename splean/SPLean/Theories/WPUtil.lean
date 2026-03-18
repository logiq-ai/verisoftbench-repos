import Lean
import SPLean.Theories.Lang
import SPLean.Theories.SepLog

open Lean Meta Elab Tactic
open val trm

abbrev XAppExtState := RBMap Name Name Name.cmp

initialize xappExtension :
    SimpleScopedEnvExtension (Name × Name) XAppExtState <-
  registerSimpleScopedEnvExtension {
    name := `xapp
    initial := { }
    addEntry := fun s (n, thm) => s.insert n thm
  }

def getPrim (t :Expr) : Expr :=
  let_expr val_prim v := t | t
  v

def getVal (t :Expr) : Expr :=
  let_expr trm_val v := t | t
  getPrim v

partial def getNestedApp (t :Expr) : Expr :=
  let_expr trm_app t _ := t | getVal t
  getNestedApp t


def getTripleFun (g : Expr) : MetaM Name := do
  let_expr triple t _ _ := g | throwError "goal is not a triple"
  let_expr trm_app t _ := t | throwError "triple term is not an application"
  let .some n := (getNestedApp t).constName? | throwError "nested application is not a constant"
  return n

def pickTripleLemma : TacticM Name := do
  let n <- getTripleFun (<- getMainTarget)
  let .some thm := (xappExtension.getState (← getEnv)).find? n | throwError "no triple lemma found"
  return thm



set_option linter.hashCommand false

elab "#hint_xapp" thm:ident : command => do
  Command.runTermElabM fun _ => do
    let thm := (<- Term.elabTerm thm none)
    let .some thmName := thm.getAppFn.constName? | throwError "invalid theorem"
    let thm <- Meta.inferType thm
    let thmFun <- Meta.forallTelescope thm fun _ thm => do
      getTripleFun thm
    xappExtension.add (thmFun, thmName)

initialize registerBuiltinAttribute {
  name := `xapp
  descr := "Adds a triple lemma to the xapp database"
  add := fun thmName _ _ => do
    MetaM.run' do
      let thm : Expr <- Term.TermElabM.run' <| Term.elabTerm (mkIdent thmName) none
      let thm <- Meta.inferType thm
      let thmFun <- Meta.forallTelescope thm fun _ thm => do
        getTripleFun thm
      xappExtension.add (thmFun, thmName)
}
