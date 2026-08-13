import Mathlib

/-!
# RH first Weyl-germ finite firewalls

This file formalizes only scalar algebra behind the first normalized Weyl-germ
coefficient and a finite counterexample showing that one derivative does not
identify a normalized Schur germ. It does not formalize Suzuki's operators,
resolvents, complex holomorphy, the xi function, zeta zeros, or RH.
-/

namespace MillenniumBraid
namespace B2Round42RH

/-- Scalar shadow of the first finite normalized Weyl coefficient. -/
noncomputable def weylDerivative (P Q : ℂ) : ℂ := -P / Q

/-- Multiplying the relative deficiency phase by a unit complex number only
rotates the first Weyl coefficient; its modulus is unchanged. -/
theorem phase_rotation_preserves_modulus
    {u z : ℂ} (hu : Complex.abs u = 1) :
    Complex.abs (u * z) = Complex.abs z := by
  rw [map_mul, hu, one_mul]

/-- Scalar parity-resolvent form `(E-O)/(E+O)`. -/
noncomputable def parityRatio (E O : ℝ) : ℝ := (E - O) / (E + O)

/-- Nonnegative even and odd energies obey the sharp triangle bound. -/
theorem abs_energy_difference_le_sum
    {E O : ℝ} (hE : 0 ≤ E) (hO : 0 ≤ O) :
    |E - O| ≤ E + O := by
  rw [abs_le]
  constructor <;> linarith

/-- The normalized parity-resolvent imbalance lies in the closed unit interval. -/
theorem parityRatio_abs_le_one
    {E O : ℝ} (hE : 0 ≤ E) (hO : 0 ≤ O)
    (hpos : 0 < E + O) :
    |parityRatio E O| ≤ 1 := by
  rw [parityRatio, abs_div, abs_of_pos hpos]
  exact (div_le_one hpos).2 (abs_energy_difference_le_sum hE hO)

/-- If the even and odd energies agree, the first coefficient vanishes. -/
theorem parityRatio_equal_energies (E : ℝ) (hE : E ≠ 0) :
    parityRatio E E = 0 := by
  simp [parityRatio, hE]

/-- If the odd energy is zero and the even energy is positive, the first
coefficient saturates the Schwarz--Pick bound. -/
theorem parityRatio_even_only
    {E : ℝ} (hE : E ≠ 0) :
    parityRatio E 0 = 1 := by
  simp [parityRatio, hE]

/-- Abstract scalar shadow of the target logarithmic-derivative quotient. -/
noncomputable def normalizedLogDerivativeTarget (L L' : ℝ) : ℝ := L' / L

/-- Two disk-polynomial germs used by the critic. -/
def linearGerm (κ x : ℝ) : ℝ := κ * x

def quadraticGerm (κ ε x : ℝ) : ℝ := κ * x + ε * x ^ 2

/-- The two critic germs have the same normalized value at zero. -/
theorem critic_germs_same_value (κ ε : ℝ) :
    linearGerm κ 0 = quadraticGerm κ ε 0 := by
  simp [linearGerm, quadraticGerm]

/-- The two critic germs have the same first derivative at zero. -/
theorem critic_germs_same_first_derivative (κ ε : ℝ) :
    HasDerivAt (linearGerm κ) κ 0 ∧
      HasDerivAt (quadraticGerm κ ε) κ 0 := by
  constructor
  · simpa [linearGerm] using (hasDerivAt_id (0 : ℝ)).const_mul κ
  · convert
      ((hasDerivAt_id (0 : ℝ)).const_mul κ).add
        (((hasDerivAt_pow 2 (0 : ℝ)).const_mul ε)) using 1 <;>
      simp [quadraticGerm]

/-- With a nonzero quadratic coefficient, the two germs are genuinely
different despite sharing value and derivative at zero. -/
theorem critic_germs_differ
    {κ ε : ℝ} (hε : ε ≠ 0) :
    linearGerm κ 1 ≠ quadraticGerm κ ε 1 := by
  simp [linearGerm, quadraticGerm, hε]

/-- On the real unit interval, `κ x + ε x^2` stays below one whenever the
coefficients are nonnegative and sum to at most one. This is the finite scalar
shadow of the two distinct normalized Schur germs. -/
theorem quadraticGerm_unit_interval_bound
    {κ ε x : ℝ}
    (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hsum : κ + ε ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ quadraticGerm κ ε x ∧ quadraticGerm κ ε x ≤ 1 := by
  constructor
  · unfold quadraticGerm
    positivity
  · have hx2 : x ^ 2 ≤ x := by nlinarith [sq_nonneg (x - 1 / 2)]
    unfold quadraticGerm
    nlinarith

#print axioms phase_rotation_preserves_modulus
#print axioms abs_energy_difference_le_sum
#print axioms parityRatio_abs_le_one
#print axioms parityRatio_equal_energies
#print axioms parityRatio_even_only
#print axioms critic_germs_same_value
#print axioms critic_germs_same_first_derivative
#print axioms critic_germs_differ
#print axioms quadraticGerm_unit_interval_bound

end B2Round42RH
end MillenniumBraid
