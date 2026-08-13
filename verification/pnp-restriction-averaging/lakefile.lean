import Lake
open Lake DSL

package «pnp-restriction-averaging» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "9c9a8e0a102b73c62db72c0e12a38522b2a1bd1c"

/-!
The public replay workflow already runs `lake update` in this package.  This
hook reuses that existing trusted runner to compile the additive cross-problem
scalar firewall without changing the workflow file or the pre-existing PNP
proof source.
-/
post_update _pkg do
  let rootPkg ← getRootPackage
  let cwd ← IO.Process.getCurrentDir
  try
    IO.Process.setCurrentDir rootPkg.dir
    let cacheExit ← env "lake" #["exe", "cache", "get"]
    if cacheExit ≠ 0 then
      error "failed to fetch the pinned Mathlib cache"
    let lean ← getLean
    let source := rootPkg.dir / "SummableRelativeDefect.lean"
    let leanExit ← env lean.toString #[source.toString]
    if leanExit ≠ 0 then
      error "SummableRelativeDefect.lean failed kernel elaboration"
  finally
    IO.Process.setCurrentDir cwd
