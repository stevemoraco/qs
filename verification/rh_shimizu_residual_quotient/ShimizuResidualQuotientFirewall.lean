import Mathlib

/-!
# Residual-quotient readout firewall

This file formalizes the finite linear-algebra obstruction behind the audited
quotient step in a claimed RH proof architecture.

For a decomposition into visible kernel, visible arithmetic, and residual
coordinates, replacing a vector by its canonical residual-free representative
preserves a linear scalar readout exactly when that readout annihilates every
residual vector.  A definition that only calls residual-blind readouts
"admissible" does not prove that a separately constructed scalar probe is
residual-blind.

No zeta function, explicit formula, spectral operator, or RH statement is
formalized here.
-/

namespace Millennium.RH.ShimizuResidualQuotientFirewall

/-- A three-channel finite model: kernel, arithmetic, and residual. -/
abbrev X := ℝ × (ℝ × ℝ)

/-- Delete the residual coordinate. -/
def canonical (x : X) : X :=
  (x.1, (x.2.1, 0))

/-- Embed a pure residual coordinate. -/
def residual (r : ℝ) : X :=
  (0, (0, r))

/-- Every vector is its canonical representative plus its residual part. -/
theorem decompose_visible_residual (x : X) :
    x = canonical x + residual x.2.2 := by
  ext <;> simp [canonical, residual]

/-- A pure residual vector has zero canonical representative. -/
theorem canonical_residual (r : ℝ) :
    canonical (residual r) = 0 := by
  ext <;> simp [canonical, residual]

/-- The scalar probe that reads the residual coordinate. -/
def residualReadout : X →ₗ[ℝ] ℝ where
  toFun x := x.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A readout factors through the residual quotient precisely when it vanishes
on every pure residual vector. -/
def ResidualBlind (L : X →ₗ[ℝ] ℝ) : Prop :=
  ∀ r, L (residual r) = 0

/-- Canonical-representative preservation is equivalent to residual
annihilation.  This is the exact missing interface in any quotient/readout
argument of this shape. -/
theorem preserves_canonical_iff_residualBlind
    (L : X →ₗ[ℝ] ℝ) :
    (∀ x, L (canonical x) = L x) ↔ ResidualBlind L := by
  constructor
  · intro h r
    have hr := h (residual r)
    rw [canonical_residual] at hr
    simpa using hr.symm
  · intro h x
    have hx : L x = L (canonical x) := by
      calc
        L x = L (canonical x + residual x.2.2) :=
          congrArg L (decompose_visible_residual x)
        _ = L (canonical x) + L (residual x.2.2) := L.map_add _ _
        _ = L (canonical x) + 0 := by rw [h x.2.2]
        _ = L (canonical x) := add_zero _
    exact hx.symm

/-- Any claimed preservation theorem necessarily pays residual annihilation. -/
theorem preservation_requires_residual_annihilation
    (L : X →ₗ[ℝ] ℝ)
    (hpres : ∀ x, L (canonical x) = L x) :
    ResidualBlind L :=
  (preserves_canonical_iff_residualBlind L).mp hpres

/-- The residual-coordinate probe is not residual-blind. -/
theorem residualReadout_not_residualBlind :
    ¬ ResidualBlind residualReadout := by
  intro h
  have h1 : residualReadout (residual 1) = 0 := h 1
  norm_num [residualReadout, residual] at h1

/-- Residual blindness cannot be omitted: one explicit linear readout changes
when its argument is replaced by the canonical representative. -/
theorem quotient_preservation_fails_without_blindness :
    ∃ L : X →ₗ[ℝ] ℝ,
      (∃ x : X, L (canonical x) ≠ L x) ∧
      ¬ ResidualBlind L := by
  refine ⟨residualReadout, ?_, residualReadout_not_residualBlind⟩
  refine ⟨residual 1, ?_⟩
  norm_num [canonical, residual, residualReadout]

/-- Same quotient class does not determine a general scalar readout. -/
theorem same_quotient_readout_counterexample :
    ∃ x y : X,
      canonical x = canonical y ∧
      residualReadout x ≠ residualReadout y := by
  refine ⟨(0, (0, 0)), (0, (0, 1)), ?_, ?_⟩
  · norm_num [canonical]
  · norm_num [residualReadout]

/-- The smallest explicit witness: deleting the residual changes the scalar
probe from one to zero while leaving both visible coordinates fixed. -/
theorem canonical_quotient_counterexample :
    let x : X := (0, (0, 1))
    canonical x = 0 ∧
      residualReadout x = 1 ∧
      residualReadout (canonical x) = 0 := by
  norm_num [canonical, residualReadout]

#print axioms decompose_visible_residual
#print axioms canonical_residual
#print axioms preserves_canonical_iff_residualBlind
#print axioms preservation_requires_residual_annihilation
#print axioms residualReadout_not_residualBlind
#print axioms quotient_preservation_fails_without_blindness
#print axioms same_quotient_readout_counterexample
#print axioms canonical_quotient_counterexample

end Millennium.RH.ShimizuResidualQuotientFirewall
