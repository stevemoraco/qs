import Mathlib

/-!
# Round 218 RH Abel pair-energy finite cores

This file formalizes only scalar energy decompositions, diagonal/off-diagonal
cancellation algebra, a zero-moment product-main-term identity, and finite
threshold implications.

It does not formalize prime sums, integrals, Laplace transforms, analytic
continuation, zeta zeros, the prime number theorem, hyperuniformity, or the
Riemann hypothesis.
-/

namespace Millennium
namespace Round218RH

theorem finite_pair_energy_decomposition
    (energy diagonal offDiagonal : ℝ)
    (hdecomp : energy = diagonal + offDiagonal) :
    offDiagonal = energy - diagonal := by
  linarith

theorem forced_offdiagonal_limit_value
    (energyLimit diagonalLimit offDiagonalLimit : ℝ)
    (hlimit : energyLimit = diagonalLimit + offDiagonalLimit) :
    offDiagonalLimit = energyLimit - diagonalLimit := by
  linarith

theorem shot_noise_cancellation_budget
    (sigma energy diagonal offDiagonal A B C : ℝ)
    (hsigma : 0 < sigma)
    (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (henergy0 : 0 ≤ energy)
    (henergy : energy ≤ A / sigma)
    (hdiag : |diagonal - C / sigma ^ 2| ≤ B / sigma)
    (hdecomp : energy = diagonal + offDiagonal) :
    |offDiagonal + C / sigma ^ 2| ≤ (A + B) / sigma := by
  have hdiagBounds :
      -(B / sigma) ≤ diagonal - C / sigma ^ 2 ∧
        diagonal - C / sigma ^ 2 ≤ B / sigma :=
    abs_le.mp hdiag
  have hAnonneg : 0 ≤ A / sigma := div_nonneg hA hsigma.le
  have hBnonneg : 0 ≤ B / sigma := div_nonneg hB hsigma.le
  apply abs_le.mpr
  constructor
  · nlinarith
  · nlinarith

theorem pair_cancellation_implies_energy_budget
    (sigma energy diagonal offDiagonal A B C : ℝ)
    (_hsigma : 0 < sigma)
    (hdiag : |diagonal - C / sigma ^ 2| ≤ B / sigma)
    (hoff : |offDiagonal + C / sigma ^ 2| ≤ A / sigma)
    (hdecomp : energy = diagonal + offDiagonal) :
    |energy| ≤ (A + B) / sigma := by
  have hdiagBounds :
      -(B / sigma) ≤ diagonal - C / sigma ^ 2 ∧
        diagonal - C / sigma ^ 2 ≤ B / sigma :=
    abs_le.mp hdiag
  have hoffBounds :
      -(A / sigma) ≤ offDiagonal + C / sigma ^ 2 ∧
        offDiagonal + C / sigma ^ 2 ≤ A / sigma :=
    abs_le.mp hoff
  apply abs_le.mpr
  constructor <;> nlinarith

theorem zero_moment_kills_factorized_pair_main
    (moment : ℝ) (hmoment : moment = 0) :
    moment * moment = 0 := by
  simp [hmoment]

theorem finite_energy_excludes_deeper_pole
    (sigma delta : ℝ)
    (hgate : delta ≤ sigma / 2) :
    2 * delta ≤ sigma := by
  linarith

theorem cofinal_energy_parameters_force_zero_depth
    (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hcofinal : ∀ eps : ℝ, 0 < eps → delta ≤ eps) :
    delta = 0 := by
  by_contra hne
  have hpos : 0 < delta := lt_of_le_of_ne hdelta (Ne.symm hne)
  have hhalf : 0 < delta / 2 := half_pos hpos
  have hbound := hcofinal (delta / 2) hhalf
  linarith

theorem small_error_cannot_cancel_positive_diagonal
    (diagonal error target : ℝ)
    (hdiag : 0 < diagonal)
    (hsmall : |error| < diagonal)
    (htarget : target = diagonal + error) :
    target ≠ 0 := by
  intro hzero
  have herror : error = -diagonal := by
    linarith
  have habs : |error| = diagonal := by
    rw [herror, abs_neg, abs_of_pos hdiag]
  linarith

#print axioms finite_pair_energy_decomposition
#print axioms forced_offdiagonal_limit_value
#print axioms shot_noise_cancellation_budget
#print axioms pair_cancellation_implies_energy_budget
#print axioms zero_moment_kills_factorized_pair_main
#print axioms finite_energy_excludes_deeper_pole
#print axioms cofinal_energy_parameters_force_zero_depth
#print axioms small_error_cannot_cancel_positive_diagonal

end Round218RH
end Millennium
