import Lake
open Lake DSL

package «pnp-restriction-averaging» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "c44e0c8ee63ca166450922a373c7409c5d26b00b"

post_update _pkg do
  let rootPkg ← getRootPackage
  let cwd ← IO.Process.getCurrentDir
  try
    IO.Process.setCurrentDir rootPkg.dir
    let cacheExit ← env "lake" #["exe", "cache", "get"]
    if cacheExit ≠ 0 then
      error "failed to fetch the pinned Mathlib cache"
    let lean ← getLean
    let sources := #[
      "SummableRelativeDefect.lean",
      "PNPDistributionalDictionaryFinite.lean",
      "PNPLowBallHighGirth.lean"
    ]
    for sourceName in sources do
      let source := rootPkg.dir / sourceName
      let leanExit ← env lean.toString #[source.toString]
      if leanExit ≠ 0 then
        error s!"{sourceName} failed kernel elaboration"
  finally
    IO.Process.setCurrentDir cwd
