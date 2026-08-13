import Lake
open Lake DSL

package round217Hodge

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

@[default_target]
lean_lib Round217Hodge where
  srcDir := "."
