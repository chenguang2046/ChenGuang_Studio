import Lake
open Lake DSL

package chenguang_core where
  version := v!"0.1.0"
  description := "ChenGuang Core: Base_64 analytic slices + Bounty_Probe formalizations (Lean 4 + mathlib)"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"

@[default_target]
lean_lib Base_64 where
  roots := #[`Base_64]
  globs := #[.submodules `Base_64]

@[default_target]
lean_lib Bounty_Probe where
  globs := #[.submodules `Bounty_Probe]
