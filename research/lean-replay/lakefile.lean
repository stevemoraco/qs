import Lake
open Lake DSL

package Round41Replay

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

lean_lib B2Round41Replay where
  roots := #[`B2Round41AdversarialCores]
