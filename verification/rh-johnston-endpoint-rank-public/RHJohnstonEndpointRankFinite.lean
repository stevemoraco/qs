import Mathlib

namespace RHJohnstonEndpointRankFinite

/-!
Finite algebraic shadow of the Johnston endpoint-response firewall.

The human theorem lives in `stevemoraco/RH` and proves that the Green response of
the symmetric endpoint pair is a Fourier multiplier with infinite rank and
infinite positive/negative inertia on `L²(ℝ)`, including both parity sectors.

This file deliberately does **not** define Fourier transforms, convolution,
`L²(ℝ)`, Plancherel theory, Johnston's kernel, zeta, or RH.  It formalizes only
the finite diagonal spine used after choosing finitely many disjoint sign bands.
-/

/-- Coordinatewise propagation by a diagonal multiplier. -/
def diagonalApply {ι : Type*} (w x : ι → ℝ) : ι → ℝ :=
  fun i => w i * x i

/-- A diagonal response with no zero multiplier is injective, regardless of the
number of propagated coordinates. -/
theorem diagonalApply_injective
    {ι : Type*} {w : ι → ℝ}
    (hw : ∀ i, w i ≠ 0) :
    Function.Injective (diagonalApply w) := by
  intro x y hxy
  funext i
  have hi : w i * x i = w i * y i := congrFun hxy i
  have hmul : w i * (x i - y i) = 0 := by
    calc
      w i * (x i - y i) = w i * x i - w i * y i := by ring
      _ = 0 := sub_eq_zero.mpr hi
  have hdiff : x i - y i = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (hw i)
  exact sub_eq_zero.mp hdiff

/-- The unit coordinate at `i`. -/
def coordinate {ι : Type*} [DecidableEq ι] (i : ι) : ι → ℝ :=
  fun j => if j = i then 1 else 0

/-- A diagonal multiplier sends a unit coordinate to the same coordinate scaled
by the corresponding weight. -/
theorem diagonalApply_coordinate
    {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (i : ι) :
    diagonalApply w (coordinate i) =
      fun j => if j = i then w i else 0 := by
  funext j
  by_cases hji : j = i
  · simp [diagonalApply, coordinate, hji]
  · simp [diagonalApply, coordinate, hji]

/-- Finite diagonal quadratic form. -/
def diagonalQuadratic
    {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) : ℝ :=
  ∑ i, w i * (x i) ^ 2

/-- The quadratic form on one unit coordinate is exactly its diagonal weight. -/
theorem diagonalQuadratic_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (i : ι) :
    diagonalQuadratic w (coordinate i) = w i := by
  classical
  simp [diagonalQuadratic, coordinate]

/-- A finite model with `n` positive and `n` negative frequency coordinates. -/
def signedWeight (n : ℕ) : Sum (Fin n) (Fin n) → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

/-- Every signed-model multiplier is nonzero. -/
theorem signedWeight_ne_zero
    (n : ℕ) (i : Sum (Fin n) (Fin n)) :
    signedWeight n i ≠ 0 := by
  cases i <;> norm_num [signedWeight]

/-- Hence the signed diagonal response is injective in every finite dimension. -/
theorem signedDiagonal_injective (n : ℕ) :
    Function.Injective (diagonalApply (signedWeight n)) := by
  exact diagonalApply_injective (signedWeight_ne_zero n)

/-- Each left coordinate is a strict positive quadratic witness. -/
theorem left_coordinate_positive
    (n : ℕ) (i : Fin n) :
    diagonalQuadratic (signedWeight n) (coordinate (Sum.inl i)) = 1 := by
  rw [diagonalQuadratic_coordinate]
  rfl

/-- Each right coordinate is a strict negative quadratic witness. -/
theorem right_coordinate_negative
    (n : ℕ) (i : Fin n) :
    diagonalQuadratic (signedWeight n) (coordinate (Sum.inr i)) = -1 := by
  rw [diagonalQuadratic_coordinate]
  rfl

/-- Arbitrarily many positive and negative coordinate witnesses coexist. -/
theorem arbitrary_signed_coordinate_witnesses (n : ℕ) :
    (∀ i : Fin n,
      diagonalQuadratic (signedWeight n) (coordinate (Sum.inl i)) = 1) ∧
    (∀ i : Fin n,
      diagonalQuadratic (signedWeight n) (coordinate (Sum.inr i)) = -1) := by
  exact ⟨left_coordinate_positive n, right_coordinate_negative n⟩

/-- No fixed finite dimension bound follows from the number of source labels:
for every proposed bound there is a larger injective propagated diagonal model. -/
theorem propagated_dimension_exceeds_any_bound (bound : ℕ) :
    ∃ n : ℕ,
      bound < n ∧
      Function.Injective
        (diagonalApply (fun _ : Fin n => (1 : ℝ))) := by
  refine ⟨bound + 1, Nat.lt_succ_self bound, ?_⟩
  apply diagonalApply_injective
  intro i
  norm_num

/-- Multiplying every diagonal weight by `-1` preserves injectivity and swaps
positive/negative coordinate values. -/
theorem sign_flip_preserves_injectivity
    {ι : Type*} {w : ι → ℝ}
    (hw : ∀ i, w i ≠ 0) :
    Function.Injective (diagonalApply (fun i => -w i)) := by
  apply diagonalApply_injective
  intro i
  exact neg_ne_zero.mpr (hw i)

#print axioms diagonalApply_injective
#print axioms diagonalApply_coordinate
#print axioms diagonalQuadratic_coordinate
#print axioms signedWeight_ne_zero
#print axioms signedDiagonal_injective
#print axioms left_coordinate_positive
#print axioms right_coordinate_negative
#print axioms arbitrary_signed_coordinate_witnesses
#print axioms propagated_dimension_exceeds_any_bound
#print axioms sign_flip_preserves_injectivity

end RHJohnstonEndpointRankFinite
