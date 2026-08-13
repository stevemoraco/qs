import Lake
open Lake DSL

package «millennium-braid-unified» where
  name := "millennium-braid-unified"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

lean_lib «MillenniumBraidUnified» where
  roots := #[`MillenniumBraidUnified]
