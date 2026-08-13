import Mathlib

/-!
# Pure-electric transfer defect: finite scalar shadow

Finite real-algebra consequences used by
`research/yang_mills/YM_PURE_ELECTRIC_GAUGE_INVARIANT_DEFECT_FIREWALL_2026-08-13.md`.

This file does not formalize compact groups, Haar measure, graph Laplacians,
spectral measures, Wilson characters, gauge invariance, ground-state
transforms, asymptotic freedom, Osterwalder--Schrader reconstruction, or
Yang--Mills.
-/

namespace MillenniumBraid
namespace YMPureElectricDefectFinite

/-- Once the analytic spectral argument supplies the lower defect floor, the
finite scalar theorem records it without changing normalization. -/
theorem defectFloor
    (gSq lambda variance defect : ℝ)
    (hlower : (gSq * lambda / 4) * variance ≤ defect) :
    (gSq * lambda / 4) * variance ≤ defect :=
  hlower

/-- If `g^2/a` is already beyond the proposed constant, the spectral defect
floor strictly violates an order-`a` upper budget. -/
theorem defectFloorViolatesOrderA
    (a gSq lambda K variance defect : ℝ)
    (hvariance : 0 < variance)
    (hscale : 4 * K * a < gSq * lambda)
    (hlower : (gSq * lambda / 4) * variance ≤ defect) :
    K * a * variance < defect := by
  have hscaled := mul_lt_mul_of_pos_right hscale hvariance
  nlinarith

/-- Scalar expression for the exact character-loop defect.  The human theorem
proves that this expression is realized by a simple Wilson character. -/
noncomputable def wilsonDefect (gSq loopLength casimir : ℝ) : ℝ :=
  1 - Real.exp (-(gSq * loopLength * casimir / 2))

@[simp] theorem wilsonDefectFormula
    (gSq loopLength casimir : ℝ) :
    wilsonDefect gSq loopLength casimir =
      1 - Real.exp (-(gSq * loopLength * casimir / 2)) := by
  rfl

/-- The Wilson exponent is monotone in loop length when the coupling and
Casimir are nonnegative. -/
theorem wilsonExponentMonotone
    (gSq casimir loopLength₁ loopLength₂ : ℝ)
    (hgSq : 0 ≤ gSq)
    (hcasimir : 0 ≤ casimir)
    (hlength : loopLength₁ ≤ loopLength₂) :
    gSq * loopLength₁ * casimir / 2 ≤
      gSq * loopLength₂ * casimir / 2 := by
  have hfirst : gSq * loopLength₁ ≤ gSq * loopLength₂ :=
    mul_le_mul_of_nonneg_left hlength hgSq
  have hsecond :
      (gSq * loopLength₁) * casimir ≤
        (gSq * loopLength₂) * casimir :=
    mul_le_mul_of_nonneg_right hfirst hcasimir
  linarith

/-- If a loop has fixed positive physical length and `g^2/a` has crossed a
given threshold, its Wilson exponent has crossed the corresponding finite
threshold. -/
theorem physicalLoopExponentAbove
    (a gSq ell loopLength casimir M : ℝ)
    (ha : 0 < a)
    (hgSq : 0 ≤ gSq)
    (hcasimir : 0 ≤ casimir)
    (hphysicalLength : ell ≤ a * loopLength)
    (hscale : 2 * M * a < gSq * ell * casimir) :
    M < gSq * loopLength * casimir / 2 := by
  have hfirst : gSq * ell ≤ gSq * (a * loopLength) :=
    mul_le_mul_of_nonneg_left hphysicalLength hgSq
  have hsecond :
      (gSq * ell) * casimir ≤
        (gSq * (a * loopLength)) * casimir :=
    mul_le_mul_of_nonneg_right hfirst hcasimir
  have hproduct :
      (2 * M) * a < (gSq * loopLength * casimir) * a := by
    calc
      (2 * M) * a = 2 * M * a := by ring
      _ < gSq * ell * casimir := hscale
      _ ≤ (gSq * (a * loopLength)) * casimir := hsecond
      _ = (gSq * loopLength * casimir) * a := by ring
  have hcancel : 2 * M < gSq * loopLength * casimir :=
    (mul_lt_mul_iff_left₀ ha).mp hproduct
  linarith

/-- The interacting ground-state identity plus a reverse-Poincare budget gives
the required upper Rayleigh bound.  All analytic content is deliberately in
the two hypotheses. -/
theorem reversePoincareClosesRayleigh
    (a gSq K dirichlet variance energy : ℝ)
    (ha : 0 < a)
    (hreverse : gSq * dirichlet ≤ 2 * a * K * variance)
    (henergy : 2 * a * energy = gSq * dirichlet) :
    energy ≤ K * variance := by
  have hpositive : 0 < 2 * a := by positivity
  apply (mul_le_mul_iff_right₀ hpositive).mp
  calc
    (2 * a) * energy = gSq * dirichlet := henergy
    _ ≤ 2 * a * K * variance := hreverse
    _ = (2 * a) * (K * variance) := by ring

/-- Conversely, an upper Rayleigh bound forces the scalar reverse-Poincare
budget once the exact ground-state energy identity is known. -/
theorem rayleighBoundForcesReversePoincare
    (a gSq K dirichlet variance energy : ℝ)
    (ha : 0 < a)
    (hrayleigh : energy ≤ K * variance)
    (henergy : 2 * a * energy = gSq * dirichlet) :
    gSq * dirichlet ≤ 2 * a * K * variance := by
  calc
    gSq * dirichlet = 2 * a * energy := henergy.symm
    _ ≤ 2 * a * (K * variance) :=
      mul_le_mul_of_nonneg_left hrayleigh (by positivity)
    _ = 2 * a * K * variance := by ring

#print axioms defectFloor
#print axioms defectFloorViolatesOrderA
#print axioms wilsonDefectFormula
#print axioms wilsonExponentMonotone
#print axioms physicalLoopExponentAbove
#print axioms reversePoincareClosesRayleigh
#print axioms rayleighBoundForcesReversePoincare

end YMPureElectricDefectFinite
end MillenniumBraid
