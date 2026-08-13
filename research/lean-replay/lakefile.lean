import Lake
open Lake DSL

package Round41Replay

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.31.0"

@[default_target]
lean_lib Round41Replay where
  roots := #[`B2Round41AdversarialCores]
