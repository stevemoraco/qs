import Lake
open Lake DSL

package «bsd-gv-semiprime-density»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

lean_lib BSDGVSemiprimeDensity where
  roots := #[
    `BSDGVSemiprimeDensity,
    `BSDGVAsymptoticAggregation,
    `BSDGVDiscriminantHeight
  ]
