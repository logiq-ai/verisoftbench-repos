
import Juvix.Core.Main.Language.Base

namespace Juvix.Core.Main

mutual
  inductive Value : Type where
    | unit : Value
    | const : Constant → Value
    | constr_app : (constr : Name) → (args_rev : List Value) → Value
    | closure : (env : List Object) → (value : Expr) → Value
    deriving Inhabited

  inductive Object : Type where
    | value : Value → Object
    | delayed : (env : List Object) → Expr → Object
    deriving Inhabited
end

abbrev Env : Type := List Object
abbrev cons_value (v : Value) (env : Env) : Env := Object.value v :: env

infixr:50 " ∷ " => cons_value

end Juvix.Core.Main
