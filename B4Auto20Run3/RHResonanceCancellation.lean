import Mathlib

namespace B4Auto20Run3

/-- BANKER: for the paired tent-ray resonance coefficient, the only finite
algebraic cancellation mechanism is the exact multiplicity relation
`mDouble = 4 * mGamma`. This is finite complex-field algebra only. -/
theorem rh_paired_resonance_zero_iff
    (mGamma mDouble gamma : ℂ) (hgamma : gamma ≠ 0) :
    (4 * mGamma - mDouble) / (8 * gamma ^ 4) = 0 ↔
      4 * mGamma = mDouble := by
  constructor
  · intro h
    have hden : (8 : ℂ) * gamma ^ 4 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 4 hgamma)
    have hnum : 4 * mGamma - mDouble = 0 := by
      apply (div_eq_zero_iff).mp h |>.resolve_right
      exact hden
    exact sub_eq_zero.mp hnum
  · intro h
    rw [h]
    simp

/-- CLEANER: a multiplicity mismatch prevents paired resonance cancellation. -/
theorem rh_paired_resonance_nonzero_of_mismatch
    (mGamma mDouble gamma : ℂ) (hgamma : gamma ≠ 0)
    (hmismatch : 4 * mGamma ≠ mDouble) :
    (4 * mGamma - mDouble) / (8 * gamma ^ 4) ≠ 0 := by
  intro hzero
  exact hmismatch ((rh_paired_resonance_zero_iff mGamma mDouble gamma hgamma).mp hzero)

/-- CRITIC: exact harmonic resonance can cancel completely when the multiplicity
relation is met; nonzero endpoint data alone therefore does not forbid a paired
pole cancellation. -/
theorem rh_exact_resonance_cancellation_witness :
    (4 * (1 : ℂ) - 4) / (8 * (1 : ℂ) ^ 4) = 0 := by
  norm_num

#print axioms B4Auto20Run3.rh_paired_resonance_zero_iff
#print axioms B4Auto20Run3.rh_paired_resonance_nonzero_of_mismatch
#print axioms B4Auto20Run3.rh_exact_resonance_cancellation_witness

end B4Auto20Run3
