import Mathlib
import Lean.Util.CollectAxioms

/-!
# Kernel inventory smoke test

This file validates the exact environment-level audit primitive used by the
exhaustive RH/RH-Lean integration generator.  The full private corpus is not
copied here.
-/

namespace MillenniumKernelInventorySmoke

theorem foundation_only : True := True.intro

open Lean

private def auditedTheorems : Array Lean.Name :=
  #[``MillenniumKernelInventorySmoke.foundation_only]

private def foundationAllowed (name : Lean.Name) : Bool :=
  name == ``propext ||
  name == ``Classical.choice ||
  name == ``Quot.sound

open Lean Elab Command

elab "#auditSmokeTheorems" : command => do
  let env ← getEnv
  let mut seen : Nat := 0
  for name in auditedTheorems do
    match env.find? name with
    | some (.thmInfo _) =>
        seen := seen + 1
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless foundationAllowed ax do
            throwError m!"unexpected axiom {ax} reachable from {name}"
    | some _ => throwError m!"manifest entry is not a theorem: {name}"
    | none => throwError m!"missing theorem: {name}"
  if seen != auditedTheorems.size then
    throwError m!"inventory mismatch: expected {auditedTheorems.size}, saw {seen}"
  logInfo m!"AUDITED_SMOKE_THEOREMS={seen}"

#auditSmokeTheorems

#print axioms foundation_only

end MillenniumKernelInventorySmoke
