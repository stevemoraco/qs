import Lake
open Lake DSL

package «rh-deficit-check» where
  name := "rh-deficit-check"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"
