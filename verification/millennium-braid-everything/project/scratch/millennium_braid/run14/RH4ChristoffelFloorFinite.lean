import Mathlib

namespace RHBraid

/-- Summing componentwise Christoffel inequalities gives the endpoint floor
for a sum-of-squares representation. -/
theorem sos_christoffel_floor
    {ι : Type*} [Fintype ι]
    (lam : ℝ) (energy eval : ι → ℝ)
    (hlam : 0 ≤ lam)
    (hcomponent : ∀ i, lam * (eval i) ^ 2 ≤ energy i)
    (heval : 1 ≤ ∑ i, (eval i) ^ 2) :
    lam ≤ ∑ i, energy i := by
  have hsum : ∑ i, lam * (eval i) ^ 2 ≤ ∑ i, energy i := by
    exact Finset.sum_le_sum fun i _ => hcomponent i
  have hfactor : ∑ i, lam * (eval i) ^ 2 =
      lam * ∑ i, (eval i) ^ 2 := by
    rw [Finset.mul_sum]
  rw [hfactor] at hsum
  have : lam ≤ lam * ∑ i, (eval i) ^ 2 := by
    nlinarith
  linarith

/-- The degree-one endpoint Christoffel value is the Schur complement of the
lower-right moment entry. -/
theorem christoffel_degree_one_schur
    (m0 m1 m2 : ℝ) (hm2 : m2 ≠ 0) :
    m0 - m1 ^ 2 / m2 = (m0 * m2 - m1 ^ 2) / m2 := by
  field_simp [hm2]
  ring

/-- The inverse-kernel formulation is exactly reciprocal to the Christoffel
floor whenever the floor is nonzero. -/
theorem christoffel_kernel_reciprocal
    (lam : ℝ) (hlam : lam ≠ 0) :
    1 / (1 / lam) = lam := by
  field_simp [hlam]

/-- Any upper certificate must lie above a proved hard-edge floor. -/
theorem upper_certificate_respects_floor
    (lower upper target : ℝ)
    (hfloor : lower ≤ upper) (hcert : upper ≤ target) :
    lower ≤ target := by
  linarith

/-- A positive fixed floor rules out a sequence of nonnegative certificate
objectives converging to zero. -/
theorem positive_floor_blocks_small_target
    (lower upper target : ℝ)
    (hlower : 0 < lower)
    (hfloor : lower ≤ upper)
    (hsmall : target < lower) :
    ¬ upper ≤ target := by
  linarith

end RHBraid
