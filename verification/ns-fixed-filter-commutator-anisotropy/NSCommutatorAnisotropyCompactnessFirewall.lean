import Mathlib

noncomputable section

namespace NSCommutatorAnisotropyCompactnessFirewall

/-- Scalar support weight for the concentration model.  The parameter `a`
represents amplitude and the support weight is `a^-4`. -/
def supportWeight (a : ℝ) : ℝ := 1 / a ^ 4

/-- Quadratic mass is subcritical relative to the quartic normalization. -/
theorem quadraticMass_exact {a : ℝ} (ha : a ≠ 0) :
    supportWeight a * a ^ 2 = 1 / a ^ 2 := by
  unfold supportWeight
  field_simp [ha]

/-- Cubic mass is also subcritical relative to the quartic normalization. -/
theorem cubicMass_exact {a : ℝ} (ha : a ≠ 0) :
    supportWeight a * a ^ 3 = 1 / a := by
  unfold supportWeight
  field_simp [ha]

/-- Quartic mass stays exactly one in the concentration model. -/
theorem quarticMass_exact {a : ℝ} (ha : a ≠ 0) :
    supportWeight a * a ^ 4 = 1 := by
  unfold supportWeight
  field_simp [ha]

/-- One exact bundle: lower moments decay as inverse powers of amplitude while
quartic defect remains normalized.  This is a scalar concentration model only,
not a Navier--Stokes realizability statement. -/
theorem subquartic_vs_quartic_exact {a : ℝ} (ha : a ≠ 0) :
    supportWeight a * a ^ 2 = 1 / a ^ 2 ∧
    supportWeight a * a ^ 3 = 1 / a ∧
    supportWeight a * a ^ 4 = 1 := by
  exact ⟨quadraticMass_exact ha, cubicMass_exact ha, quarticMass_exact ha⟩

/-- A linear work functional is completely blind to an additive component that
lies in its nullspace.  This is the finite algebraic analogue of discarding an
isotropic stress component after proving the relevant differential work operator
annihilates it. -/
theorem null_component_does_not_contribute
    {V : Type*} [AddCommGroup V]
    (work : V →+ ℝ) (dev iso : V)
    (hiso : work iso = 0) :
    work (dev + iso) = work dev := by
  rw [map_add, hiso, add_zero]

/-- Conversely, nonzero work cannot be carried entirely by a null component. -/
theorem nonzero_work_requires_visible_component
    {V : Type*} [AddCommGroup V]
    (work : V →+ ℝ) (dev iso : V)
    (hiso : work iso = 0)
    (hne : work (dev + iso) ≠ 0) :
    work dev ≠ 0 := by
  rw [null_component_does_not_contribute work dev iso hiso] at hne
  exact hne

/-- Exact three-eigenvalue anisotropy identity.  The left side is the squared
size of the diagonal deviator after subtracting the mean; the right side is the
pairwise eigenvalue-gap form. -/
theorem threeEigenvalueAnisotropyIdentity (a b c : ℝ) :
    let m := (a + b + c) / 3
    (a - m) ^ 2 + (b - m) ^ 2 + (c - m) ^ 2 =
      ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 3 := by
  dsimp
  ring

/-- For nonnegative covariance eigenvalues, squared deviatoric anisotropy is at
most two-thirds of squared trace.  Rank-one covariance saturates the bound. -/
theorem psdCovariance_anisotropy_le_twoThirdTraceSq
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let m := (a + b + c) / 3
    (a - m) ^ 2 + (b - m) ^ 2 + (c - m) ^ 2 ≤
      (2 / 3 : ℝ) * (a + b + c) ^ 2 := by
  dsimp
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hac : 0 ≤ a * c := mul_nonneg ha hc
  have hbc : 0 ≤ b * c := mul_nonneg hb hc
  nlinarith

/-- Rank-one covariance realizes the extremal anisotropy ratio exactly. -/
theorem rankOneCovariance_saturates_anisotropy (q : ℝ) :
    let m := (q + 0 + 0) / 3
    (q - m) ^ 2 + ((0 : ℝ) - m) ^ 2 + ((0 : ℝ) - m) ^ 2 =
      (2 / 3 : ℝ) * q ^ 2 := by
  dsimp
  ring

/-- Equal covariance eigenvalues have zero deviatoric anisotropy even when the
common covariance level is nonzero. -/
theorem isotropicCovariance_has_zero_anisotropy (q : ℝ) :
    let m := (q + q + q) / 3
    (q - m) ^ 2 + (q - m) ^ 2 + (q - m) ^ 2 = 0 := by
  dsimp
  ring

#print axioms quadraticMass_exact
#print axioms cubicMass_exact
#print axioms quarticMass_exact
#print axioms subquartic_vs_quartic_exact
#print axioms null_component_does_not_contribute
#print axioms nonzero_work_requires_visible_component
#print axioms threeEigenvalueAnisotropyIdentity
#print axioms psdCovariance_anisotropy_le_twoThirdTraceSq
#print axioms rankOneCovariance_saturates_anisotropy
#print axioms isotropicCovariance_has_zero_anisotropy

end NSCommutatorAnisotropyCompactnessFirewall
