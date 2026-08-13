import Mathlib

namespace NSNeutralAxisBogoliubovFinite

/-- Squared coefficient of the retained circular/helical polarization when a
real `2 × 2` matrix `[[a,b],[c,d]]` acts on `(1,i)/sqrt 2`.  This file
formalizes only finite scalar algebra, not Kelvin waves or Navier--Stokes. -/
def alphaSq (a b c d : ℝ) : ℝ :=
  ((a + d) ^ 2 + (b - c) ^ 2) / 4

/-- Squared coefficient of the opposite circular/helical polarization. -/
def betaSq (a b c d : ℝ) : ℝ :=
  ((a - d) ^ 2 + (b + c) ^ 2) / 4

/-- Total squared polarization gain. -/
def gainSq (a b c d : ℝ) : ℝ :=
  alphaSq a b c d + betaSq a b c d

/-- The indefinite circular-polarization norm is exactly the determinant. -/
theorem alphaSq_sub_betaSq (a b c d : ℝ) :
    alphaSq a b c d - betaSq a b c d = a * d - b * c := by
  unfold alphaSq betaSq
  ring

/-- Total gain is determinant plus twice the wrong-helicity energy. -/
theorem gainSq_eq_det_add_two_betaSq (a b c d : ℝ) :
    gainSq a b c d = (a * d - b * c) + 2 * betaSq a b c d := by
  unfold gainSq alphaSq betaSq
  ring

/-- The wrong-helicity squared coefficient is nonnegative. -/
theorem betaSq_nonneg (a b c d : ℝ) :
    0 ≤ betaSq a b c d := by
  unfold betaSq
  positivity

/-- For an area-preserving real propagator, gain squared is `1 + 2 beta²`. -/
theorem determinant_one_gain
    {a b c d : ℝ}
    (hdet : a * d - b * c = 1) :
    gainSq a b c d = 1 + 2 * betaSq a b c d := by
  calc
    gainSq a b c d = (a * d - b * c) + 2 * betaSq a b c d :=
      gainSq_eq_det_add_two_betaSq a b c d
    _ = 1 + 2 * betaSq a b c d := by rw [hdet]

/-- An area-preserving propagator cannot reduce the norm of a circular input. -/
theorem determinant_one_gain_ge_one
    {a b c d : ℝ}
    (hdet : a * d - b * c = 1) :
    1 ≤ gainSq a b c d := by
  rw [determinant_one_gain hdet]
  nlinarith [betaSq_nonneg a b c d]

/-- Exact pure-helicity return forces unit gain. -/
theorem pure_helicity_return_no_gain
    {a b c d : ℝ}
    (hdet : a * d - b * c = 1)
    (hpure : betaSq a b c d = 0) :
    gainSq a b c d = 1 := by
  rw [determinant_one_gain hdet, hpure]
  ring

/-- Cross-multiplied form of the exact wrong-helicity/gain relation. -/
theorem twice_betaSq_eq_gainSq_sub_one
    {a b c d : ℝ}
    (hdet : a * d - b * c = 1) :
    2 * betaSq a b c d = gainSq a b c d - 1 := by
  rw [determinant_one_gain hdet]
  ring

/-- If the wrong-helicity energy fraction is at most `eps < 1/2`, then the
squared gain is at most `1/(1-2 eps)`.  Thus asymptotic helicity purity forces
asymptotically unit gain. -/
theorem approximate_purity_caps_gain
    {a b c d eps : ℝ}
    (hdet : a * d - b * c = 1)
    (hgain_pos : 0 < gainSq a b c d)
    (heps : eps < 1 / 2)
    (hfrac : betaSq a b c d / gainSq a b c d ≤ eps) :
    gainSq a b c d ≤ 1 / (1 - 2 * eps) := by
  have hbeta : betaSq a b c d ≤ eps * gainSq a b c d :=
    (div_le_iff₀ hgain_pos).mp hfrac
  have hgain := determinant_one_gain hdet
  have hden : 0 < 1 - 2 * eps := by linarith
  have hmul : gainSq a b c d * (1 - 2 * eps) ≤ 1 := by
    rw [hgain]
    nlinarith
  exact (le_div_iff₀ hden).2 hmul

/-- The diagonal hyperbolic squeeze has determinant one. -/
theorem diagonal_squeeze_det_one
    {r : ℝ} (hr : r ≠ 0) :
    r * (1 / r) - 0 * 0 = 1 := by
  field_simp [hr]

/-- Exact opposite-helicity content of the diagonal squeeze. -/
theorem diagonal_squeeze_betaSq (r : ℝ) :
    betaSq r 0 0 (1 / r) = (r - 1 / r) ^ 2 / 4 := by
  unfold betaSq
  ring

/-- Exact gain of the diagonal squeeze. -/
theorem diagonal_squeeze_gainSq (r : ℝ) :
    gainSq r 0 0 (1 / r) =
      ((r + 1 / r) ^ 2 + (r - 1 / r) ^ 2) / 4 := by
  unfold gainSq alphaSq betaSq
  ring

#print axioms alphaSq_sub_betaSq
#print axioms gainSq_eq_det_add_two_betaSq
#print axioms betaSq_nonneg
#print axioms determinant_one_gain
#print axioms determinant_one_gain_ge_one
#print axioms pure_helicity_return_no_gain
#print axioms twice_betaSq_eq_gainSq_sub_one
#print axioms approximate_purity_caps_gain
#print axioms diagonal_squeeze_det_one
#print axioms diagonal_squeeze_betaSq
#print axioms diagonal_squeeze_gainSq

end NSNeutralAxisBogoliubovFinite
