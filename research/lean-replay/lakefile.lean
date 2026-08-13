import Lake
open Lake DSL

package «b2-round41-replay» where
  name := "b2-round41-replay"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

lean_lib «B2Round41Replay» where
  roots := #[`B2Round41AdversarialCores]
