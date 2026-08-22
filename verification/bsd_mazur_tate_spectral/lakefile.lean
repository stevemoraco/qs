import Lake
open Lake DSL

package «bsd-mazur-tate-spectral-verifier» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

lean_lib BSDMazurTateSpectralVerifier where
  roots := #[`BSDMazurTateSpectralExtractor]
