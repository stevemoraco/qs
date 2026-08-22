import Mathlib

/-!
# BSD: Kuga--Sato object and conjugation firewalls

This file isolates finite dimension arithmetic and a linear countermodel used to
audit a claimed all-rank BSD proof.

If a family has base dimension `b` and fiber dimension `f`, its `r`-fold fiber
power has the expected dimension `b + r*f`.  For a universal elliptic curve over
a modular curve, `b=f=1`, hence the dimension is `r+1`, not `2r` once `r>=2`.
For a fixed elliptic curve, the direct product has dimension `r`, and its full
diagonal has codimension `r-1`, not `r`.

The file also records that membership in a `-1` eigenspace of an involution does
not force a vector to vanish.

These are finite scalar/type firewalls only.  They do not formalize schemes,
Kuga--Sato varieties, Chow groups, heights, Euler systems, L-functions, or BSD.
-/

namespace Millennium.BSD.KugaSatoObjectFirewall

/-- Expected dimension of an `r`-fold fiber power of a family with base
dimension `baseDim` and relative fiber dimension `fiberDim`. -/
def fiberPowerDim (baseDim fiberDim r : ℕ) : ℕ :=
  baseDim + r * fiberDim

/-- A universal elliptic curve over a modular curve has base and fiber dimension
one, so its `r`-fold fiber power has dimension `r+1`. -/
theorem universalEllipticFiberPower_dim (r : ℕ) :
    fiberPowerDim 1 1 r = r + 1 := by
  simp [fiberPowerDim, Nat.add_comm]

/-- The claimed dimension `2r` disagrees with `r+1` for every `r>=2`. -/
theorem universalFiberPower_not_two_r
    {r : ℕ} (hr : 2 ≤ r) :
    fiberPowerDim 1 1 r ≠ 2 * r := by
  rw [universalEllipticFiberPower_dim]
  omega

/-- Exact first diagnostic: the double fiber product has dimension three, not
four. -/
theorem doubleFiberProduct_dimension_gap :
    fiberPowerDim 1 1 2 = 3 ∧ fiberPowerDim 1 1 2 ≠ 4 := by
  norm_num [fiberPowerDim]

/-- A direct product of `r` fixed curves has dimension `r`. -/
def fixedCurveProductDim (r : ℕ) : ℕ := r

/-- A fixed-curve product also cannot have dimension `2r` when `r>0`. -/
theorem fixedCurveProduct_not_two_r
    {r : ℕ} (hr : 0 < r) :
    fixedCurveProductDim r ≠ 2 * r := by
  simp [fixedCurveProductDim]
  omega

/-- The full diagonal of one curve inside its `r`-fold product has codimension
`r-1`. -/
def fixedCurveDiagonalCodim (r : ℕ) : ℕ := r - 1

/-- For every positive `r`, the simple diagonal codimension `r-1` is not `r`. -/
theorem diagonalCodim_not_r
    {r : ℕ} (hr : 0 < r) :
    fixedCurveDiagonalCodim r ≠ r := by
  simp [fixedCurveDiagonalCodim]
  omega

/-- At `r=1`, the full diagonal has codimension zero, so it cannot be a
codimension-one point-difference cycle merely by definition. -/
theorem rankOne_diagonal_codim_zero :
    fixedCurveDiagonalCodim 1 = 0 ∧ fixedCurveDiagonalCodim 1 ≠ 1 := by
  norm_num [fixedCurveDiagonalCodim]

/-- Scalar model of an involution acting by `-1`. -/
def signInvolution (x : ℝ) : ℝ := -x

/-- The scalar `1` is a nonzero `-1` eigenvector. -/
theorem nonzero_minus_one_eigenvector :
    (1 : ℝ) ≠ 0 ∧ signInvolution 1 = -(1 : ℝ) := by
  norm_num [signInvolution]

/-- Therefore the abstract inference “lies in the minus-one eigenspace, hence
vanishes” is false. -/
theorem minus_one_eigenspace_does_not_force_zero :
    ∃ x : ℝ, x ≠ 0 ∧ signInvolution x = -x := by
  exact ⟨1, nonzero_minus_one_eigenvector⟩

#print axioms universalEllipticFiberPower_dim
#print axioms universalFiberPower_not_two_r
#print axioms doubleFiberProduct_dimension_gap
#print axioms fixedCurveProduct_not_two_r
#print axioms diagonalCodim_not_r
#print axioms rankOne_diagonal_codim_zero
#print axioms nonzero_minus_one_eigenvector
#print axioms minus_one_eigenspace_does_not_force_zero

end Millennium.BSD.KugaSatoObjectFirewall
