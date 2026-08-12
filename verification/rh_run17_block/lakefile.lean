import Lake
open Lake DSL

package «rh-run17-block» where
  name := "rh-run17-block"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

lean_lib «RHDyadicBlockFinite» where
  roots := #[`RHDyadicBlockFinite]
