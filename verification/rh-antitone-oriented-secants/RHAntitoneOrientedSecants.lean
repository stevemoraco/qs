import Mathlib

/-!
# Endpoint bounds for oriented integrals of antitone kernels

For an antitone real kernel `q` on the unordered interval joining `a` and `b`,
the oriented integral is trapped between the two endpoint rectangles:

`(b-a) q(b) <= integral_a^b q <= (b-a) q(a)`.

The statement is deliberately orientation-free: it remains valid when `b<a`.
This is the generic analytic bridge used by the signed Robin--Johnston secant
estimate.
-/

open MeasureTheory Set
open scoped Interval

namespace RHAntitoneOrientedSecants

/-- Lower endpoint-rectangle bound in the standard orientation `a <= b`. -/
theorem antitone_integral_lower_of_le
    (q : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hq : AntitoneOn q (uIcc a b)) :
    (b - a) * q b ≤ ∫ x in a..b, q x := by
  have hqint : IntervalIntegrable q volume a b := hq.intervalIntegrable
  calc
    (b - a) * q b = ∫ _x in a..b, q b := by simp
    _ ≤ ∫ x in a..b, q x := by
      apply intervalIntegral.integral_mono_on hab intervalIntegrable_const hqint
      intro x hx
      apply hq
      · simpa [uIcc_of_le hab] using hx
      · exact right_mem_uIcc
      · exact hx.2

/-- Upper endpoint-rectangle bound in the standard orientation `a <= b`. -/
theorem antitone_integral_upper_of_le
    (q : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hq : AntitoneOn q (uIcc a b)) :
    (∫ x in a..b, q x) ≤ (b - a) * q a := by
  have hqint : IntervalIntegrable q volume a b := hq.intervalIntegrable
  calc
    (∫ x in a..b, q x) ≤ ∫ _x in a..b, q a := by
      apply intervalIntegral.integral_mono_on hab hqint intervalIntegrable_const
      intro x hx
      apply hq
      · exact left_mem_uIcc
      · simpa [uIcc_of_le hab] using hx
      · exact hx.1
    _ = (b - a) * q a := by simp

/-- Lower endpoint-rectangle bound for an oriented integral, with no ordering
assumption on the endpoints. -/
theorem antitone_oriented_integral_lower
    (q : ℝ → ℝ) (a b : ℝ)
    (hq : AntitoneOn q (uIcc a b)) :
    (b - a) * q b ≤ ∫ x in a..b, q x := by
  rcases le_total a b with hab | hba
  · exact antitone_integral_lower_of_le q a b hab hq
  · have hq' : AntitoneOn q (uIcc b a) := by
      simpa [uIcc_comm] using hq
    have hu := antitone_integral_upper_of_le q b a hba hq'
    calc
      (b - a) * q b = -((a - b) * q b) := by ring
      _ ≤ -(∫ x in b..a, q x) := neg_le_neg hu
      _ = ∫ x in a..b, q x := by
        rw [intervalIntegral.integral_symm]
        simp

/-- Upper endpoint-rectangle bound for an oriented integral, with no ordering
assumption on the endpoints. -/
theorem antitone_oriented_integral_upper
    (q : ℝ → ℝ) (a b : ℝ)
    (hq : AntitoneOn q (uIcc a b)) :
    (∫ x in a..b, q x) ≤ (b - a) * q a := by
  rcases le_total a b with hab | hba
  · exact antitone_integral_upper_of_le q a b hab hq
  · have hq' : AntitoneOn q (uIcc b a) := by
      simpa [uIcc_comm] using hq
    have hl := antitone_integral_lower_of_le q b a hba hq'
    calc
      (∫ x in a..b, q x) = -(∫ x in b..a, q x) := by
        rw [intervalIntegral.integral_symm]
        simp
      _ ≤ -((a - b) * q a) := neg_le_neg hl
      _ = (b - a) * q a := by ring

/-- The two endpoint bounds packaged as one interval statement. -/
theorem antitone_oriented_integral_mem_Icc
    (q : ℝ → ℝ) (a b : ℝ)
    (hq : AntitoneOn q (uIcc a b)) :
    (∫ x in a..b, q x) ∈
      Set.Icc ((b - a) * q b) ((b - a) * q a) := by
  constructor
  · exact antitone_oriented_integral_lower q a b hq
  · exact antitone_oriented_integral_upper q a b hq

/-- Abstract signed Robin--Johnston secant transfer. -/
theorem signed_secant_transfer
    (q : ℝ → ℝ)
    (p m L buffer robin : ℝ)
    (hL : 0 ≤ L)
    (hq : AntitoneOn q (uIcc m p))
    (hidentity : robin = buffer + L * (∫ u in m..p, q u)) :
    buffer + (L * (p - m)) * q p ≤ robin ∧
      robin ≤ buffer + (L * (p - m)) * q m := by
  have hlo := antitone_oriented_integral_lower q m p hq
  have hup := antitone_oriented_integral_upper q m p hq
  constructor
  · rw [hidentity]
    nlinarith [mul_le_mul_of_nonneg_left hlo hL]
  · rw [hidentity]
    nlinarith [mul_le_mul_of_nonneg_left hup hL]

end RHAntitoneOrientedSecants

#print axioms RHAntitoneOrientedSecants.antitone_integral_lower_of_le
#print axioms RHAntitoneOrientedSecants.antitone_integral_upper_of_le
#print axioms RHAntitoneOrientedSecants.antitone_oriented_integral_lower
#print axioms RHAntitoneOrientedSecants.antitone_oriented_integral_upper
#print axioms RHAntitoneOrientedSecants.antitone_oriented_integral_mem_Icc
#print axioms RHAntitoneOrientedSecants.signed_secant_transfer
