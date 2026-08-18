import Mathlib

namespace Millennium.RH

/--
Finite scalar moment form for the q-adapted Run10ar witness
  p_q(y) = y^2 + 2*q*y.
For an actual random variable Y this is
  E[(q-Y) * p_q(Y)^2]
when mu_j = E[Y^j].  The first and third moments cancel identically.
This file deliberately formalizes only the scalar algebra.
-/
def run10arMomentWitness
    (q mu2 mu4 mu5 : ℝ) : ℝ :=
  4 * q ^ 3 * mu2 - 3 * q * mu4 - mu5

/-- Exact pointwise polynomial identity behind the q-adapted moment witness. -/
theorem run10ar_pointwise_identity (q y : ℝ) :
    (q - y) * (y ^ 2 + 2 * q * y) ^ 2 =
      4 * q ^ 3 * y ^ 2 - 3 * q * y ^ 4 - y ^ 5 := by
  ring

/-- The q=1 specialization is the signed fourth/fifth moment combination. -/
theorem run10ar_at_one (mu2 mu4 mu5 : ℝ) :
    run10arMomentWitness 1 mu2 mu4 mu5 = 4 * mu2 - 3 * mu4 - mu5 := by
  simp [run10arMomentWitness]

/--
A completely explicit finite shell at q=101/100.  The analytic/probabilistic
interpretation of the `mu_j` as moments is intentionally not encoded.
-/
theorem run10ar_robust_negative_witness
    (mu2 mu4 mu5 : ℝ)
    (h2 : mu2 ≤ (101 : ℝ) / 100)
    (h4 : (3 : ℝ) / 2 ≤ mu4)
    (h5 : -(1 : ℝ) / 100 ≤ mu5) :
    run10arMomentWitness ((101 : ℝ) / 100) mu2 mu4 mu5 ≤ -(3 : ℝ) / 10 := by
  dsimp [run10arMomentWitness]
  nlinarith

#print axioms run10ar_pointwise_identity
#print axioms run10ar_at_one
#print axioms run10ar_robust_negative_witness

end Millennium.RH
