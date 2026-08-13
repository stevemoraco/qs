import Mathlib

/-!
# Carleman determinant scalar firewall

This file formalizes only the one-eigenvalue scalar factor and elementary
near-resonance inequalities used in the round-42 Yang--Mills audit. It does
not formalize Hilbert spaces, Schatten ideals, Fredholm determinants, spectra,
operator analyticity, gauge theory, OS reconstruction, or Yang--Mills.
-/

namespace MillenniumBraid
namespace B2Round42YM

/-- Scalar modified-determinant factor associated with one eigenvalue. -/
noncomputable def modifiedFactor (lambda : ℝ) : ℝ :=
  (1 - lambda) * Real.exp lambda

/-- Eigenvalue one makes the modified determinant factor vanish exactly. -/
theorem modifiedFactor_at_one :
    modifiedFactor 1 = 0 := by
  simp [modifiedFactor]

/-- The claimed positive exponential lower bound fails at eigenvalue one for
every real constant `c`. -/
theorem no_universal_exponential_lower_bound (c : ℝ) :
    ¬ Real.exp (-c * (1 : ℝ) ^ 2) ≤ |modifiedFactor 1| := by
  rw [modifiedFactor_at_one, abs_zero]
  exact not_le_of_gt (Real.exp_pos _)

/-- Exact scalar factor for an invertible near-resonance eigenvalue `1-eps`. -/
theorem near_resonance_factor_identity (eps : ℝ) :
    modifiedFactor (1 - eps) = eps * Real.exp (1 - eps) := by
  unfold modifiedFactor
  ring

/-- Near-resonance operators remain inside the unit scalar norm ball when
`eps` lies in `[0,1]`. -/
theorem near_resonance_norm_sq_le_one
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    (1 - eps) ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg eps]

/-- An abstract exponential upper bound turns a sufficiently small positive
resonance distance into an arbitrarily small determinant factor. -/
theorem near_resonance_factor_lt
    {eps E L : ℝ}
    (heps : 0 < eps)
    (hE : Real.exp (1 - eps) < E)
    (hEL : eps * E ≤ L) :
    |modifiedFactor (1 - eps)| < L := by
  rw [near_resonance_factor_identity, abs_mul,
    abs_of_pos heps, abs_of_pos (Real.exp_pos _)]
  have hmul : eps * Real.exp (1 - eps) < eps * E :=
    mul_lt_mul_of_pos_left hE heps
  exact lt_of_lt_of_le hmul hEL

/-- Invertibility of the scalar `I-A_eps` is exactly positivity/nonzeroness of
`eps`; it does not supply a uniform determinant lower bound. -/
theorem near_resonance_complement_nonzero
    {eps : ℝ} (heps : 0 < eps) :
    1 - (1 - eps) ≠ 0 := by
  linarith

/-- Divergent cutoff majorants cannot be uniformly bounded: the elementary
sequence `L` itself is finite at every cutoff and unbounded globally. -/
theorem finite_cutoffs_do_not_give_uniform_bound :
    ¬ ∃ C : ℕ, ∀ L : ℕ, L ≤ C := by
  rintro ⟨C, hC⟩
  have := hC (C + 1)
  omega

#print axioms modifiedFactor_at_one
#print axioms no_universal_exponential_lower_bound
#print axioms near_resonance_factor_identity
#print axioms near_resonance_norm_sq_le_one
#print axioms near_resonance_factor_lt
#print axioms near_resonance_complement_nonzero
#print axioms finite_cutoffs_do_not_give_uniform_bound

end B2Round42YM
end MillenniumBraid
