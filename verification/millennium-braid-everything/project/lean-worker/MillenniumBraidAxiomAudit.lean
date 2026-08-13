import MillenniumBraidAll
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean
open Lean.Elab Command

namespace MillenniumBraidAxiomAudit

/-- Exact modules admitted to the trusted finite research bank. -/
def trustedModules : NameSet := NameSet.ofArray #[
  `MillenniumBraidAll,
  `BSDToupinHaarInversionFirewall,
  `HodgeRationalIntegralFirewall,
  `NSSelectiveLerayAtom,
  `PNPParityWordInjection,
  `PerelmanCompletionRouteEquivalenceFirewall,
  `RHPureSimpleZeroNoCoercivity,
  `SeventhObjectRouteEquivalenceFirewall,
  `YMJacobsenActivityFirewall
]

/-- Foundations accepted by this audit. No theorem-specific axiom is allowed. -/
def acceptedFoundationAxioms : NameSet :=
  NameSet.ofArray #[``propext, ``Quot.sound, ``Classical.choice]

private def isTrustedTheorem (env : Environment) (n : Name)
    (info : ConstantInfo) : Bool :=
  info.isTheorem && match env.getModuleIdxFor? n with
  | some idx => trustedModules.contains env.header.moduleNames[idx]!
  | none => false

/--
Audit every theorem whose defining module belongs to the trusted bank.
The command writes a complete theorem-by-theorem TSV and fails elaboration
if any dependency axiom lies outside the accepted foundation allowlist.
-/
elab "#audit_braid_axioms" : command => do
  let env ← getEnv
  let theorems := env.constants.toList.filterMap (fun (n, i) =>
      if isTrustedTheorem env n i then some n else none)
    |>.toArray
  let mut bad : Array (Name × Array Name) := #[]
  let mut rows : Array String := #[]
  for n in theorems do
    let axs ← Lean.collectAxioms n
    let axArray := axs.toArray
    let unexpected := axArray.filter fun ax =>
      !acceptedFoundationAxioms.contains ax
    rows := rows.push <|
      "THEOREM\t" ++ n.toString ++ "\tAXIOMS\t" ++
        String.intercalate "," (axArray.toList.map Name.toString)
    unless unexpected.isEmpty do
      bad := bad.push (n, unexpected)
  rows := rows.push <|
    "SUMMARY\ttrusted_modules\t9\ttheorems\t" ++
      toString theorems.size ++ "\tunexpected\t" ++ toString bad.size
  IO.FS.writeFile "unified-axioms.tsv"
    (String.intercalate "\n" rows.toList ++ "\n")
  unless bad.isEmpty do
    let detail := bad.foldl (init := "") fun s (n, axs) =>
      s ++ "\n" ++ n.toString ++ ": " ++
        String.intercalate ", " (axs.toList.map Name.toString)
    throwError "unexpected axioms in trusted theorem bank:{detail}"
  logInfo m!"axiom audit PASS: {theorems.size} theorems; accepted axioms only"

#audit_braid_axioms

end MillenniumBraidAxiomAudit
