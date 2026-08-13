import Init

namespace RHSemilocalRealityPositivity

/-- The quadratic form of a diagonal two-level spectral model. -/
def diagonalForm (lambda₀ lambda₁ x₀ x₁ : Int) : Int :=
  lambda₀ * x₀ * x₀ + lambda₁ * x₁ * x₁

/-- Positive semidefiniteness of the diagonal form on the integral test lattice. -/
def IsPositiveSemidefinite (lambda₀ lambda₁ : Int) : Prop :=
  ∀ x₀ x₁ : Int, 0 ≤ diagonalForm lambda₀ lambda₁ x₀ x₁

/-- A perfectly cutoff-stable family with two real (indeed integral) spectral values. -/
def stableFamily (_cutoff : Nat) (x₀ x₁ : Int) : Int :=
  diagonalForm (-1) 1 x₀ x₁

/-- The negative spectral weight gives a negative value on the first basis vector. -/
theorem negative_unit_value :
    diagonalForm (-1) 1 1 0 = -1 := by
  decide

/-- The diagonal self-adjoint model with spectral values `-1` and `1` is not positive semidefinite. -/
theorem integral_diagonal_spectrum_not_psd :
    ¬ IsPositiveSemidefinite (-1) 1 := by
  intro h
  have hx : 0 ≤ diagonalForm (-1) 1 1 0 := h 1 0
  have hnot : ¬ (0 ≤ diagonalForm (-1) 1 1 0) := by
    decide
  exact hnot hx

/-- The family is exactly stable in the cutoff parameter. -/
theorem exact_cutoff_stability
    (m n : Nat) (x₀ x₁ : Int) :
    stableFamily m x₀ x₁ = stableFamily n x₀ x₁ := by
  rfl

/-- Exact cutoff stability can coexist with a permanently negative test vector. -/
theorem stable_family_has_negative_vector :
    ∀ cutoff : Nat, stableFamily cutoff 1 0 = -1 := by
  intro cutoff
  decide

/-- Real/integral diagonal spectral data plus exact form stability do not imply positivity. -/
theorem reality_and_stability_do_not_force_positivity :
    (∀ (m n : Nat) (x₀ x₁ : Int),
      stableFamily m x₀ x₁ = stableFamily n x₀ x₁) ∧
    ¬ IsPositiveSemidefinite (-1) 1 := by
  constructor
  · intro m n x₀ x₁
    exact exact_cutoff_stability m n x₀ x₁
  · exact integral_diagonal_spectrum_not_psd

/-- A square with a signed spectral coefficient need not be nonnegative. -/
def signedSquare (weight x : Int) : Int := weight * x * x

/-- The phrase "sum of squares" is sign-safe only after nonnegative weights are proved. -/
theorem negative_weighted_square_is_negative :
    signedSquare (-1) 1 = -1 := by
  decide

#print axioms negative_unit_value
#print axioms integral_diagonal_spectrum_not_psd
#print axioms exact_cutoff_stability
#print axioms stable_family_has_negative_vector
#print axioms reality_and_stability_do_not_force_positivity
#print axioms negative_weighted_square_is_negative

end RHSemilocalRealityPositivity
