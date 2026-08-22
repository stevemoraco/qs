import Lake
open Lake DSL

package «millennium-braid-unified-verifier»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

lean_lib BraidVerifier
