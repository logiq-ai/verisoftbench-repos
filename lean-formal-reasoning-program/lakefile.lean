import Lake
open Lake DSL

package «frap» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.14.0"

require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.14.0"

@[default_target]
lean_lib «Frap» where
