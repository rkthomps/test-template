import Lake
open Lake DSL

package "assignments" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require "leanprover-community" / "mathlib"

require autograder from git "https://github.com/rkthomps/lean4-autograder-main" @ "master"

@[default_target]
lean_lib «Assignments» where
  -- add any library configuration options here
