import Init

namespace MillenniumHodgeFoundation

/-- Codimension bookkeeping for a self-correspondence on an `n`-fold.
A codimension-`r` correspondence shifts cohomological degree by `2 * (r - n)`;
we retain the half-shift `r - n`. -/
def halfShift (n r : Nat) : Int := Int.ofNat r - Int.ofNat n

/-- Codimension of the composite of codimension-`r` and codimension-`s`
self-correspondences on an `n`-fold. -/
def compositeCodim (n r s : Nat) : Nat := r + s - n

/-- Transposition preserves codimension on a self-product. -/
def transposeCodim (r : Nat) : Nat := r

/-- The `m`-fold positive Lefschetz power on an `n`-fold has codimension `n+m`. -/
def lefschetzPowerCodim (n m : Nat) : Nat := n + m

/-- A correspondence lowering cohomological degree by `2m` must have codimension `n-m`. -/
def inverseRequiredCodim (n m : Nat) : Nat := n - m

/-- On a curve, the Lefschetz correspondence has codimension two. -/
theorem projectiveLine_lefschetz_codim :
    lefschetzPowerCodim 1 1 = 2 := by
  decide

/-- Transposing that correspondence still leaves codimension two. -/
theorem projectiveLine_transpose_codim :
    transposeCodim (lefschetzPowerCodim 1 1) = 2 := by
  decide

/-- The inverse `H^2 -> H^0` on a curve requires codimension zero. -/
theorem projectiveLine_inverse_required_codim :
    inverseRequiredCodim 1 1 = 0 := by
  decide

/-- Therefore the transpose of the positive Lefschetz correspondence cannot
have the codimension required for the inverse Hard-Lefschetz map. -/
theorem projectiveLine_transpose_not_inverse :
    transposeCodim (lefschetzPowerCodim 1 1) ≠ inverseRequiredCodim 1 1 := by
  decide

/-- Two codimension-two self-correspondences on a curve compose in codimension three. -/
theorem projectiveLine_square_codim :
    compositeCodim 1 2 2 = 3 := by
  decide

/-- The positive Lefschetz correspondence has half-shift `+1`. -/
theorem projectiveLine_positive_halfShift :
    halfShift 1 (lefschetzPowerCodim 1 1) = 1 := by
  decide

/-- A correspondence realizing the inverse requires half-shift `-1`. -/
theorem projectiveLine_inverse_halfShift :
    halfShift 1 (inverseRequiredCodim 1 1) = -1 := by
  decide

/-- Transposition preserves the positive half-shift and therefore cannot turn it
into the negative half-shift of the inverse. -/
theorem projectiveLine_transpose_shift_not_inverse :
    halfShift 1 (transposeCodim (lefschetzPowerCodim 1 1)) ≠
      halfShift 1 (inverseRequiredCodim 1 1) := by
  decide

#print axioms projectiveLine_lefschetz_codim
#print axioms projectiveLine_transpose_codim
#print axioms projectiveLine_inverse_required_codim
#print axioms projectiveLine_transpose_not_inverse
#print axioms projectiveLine_square_codim
#print axioms projectiveLine_positive_halfShift
#print axioms projectiveLine_inverse_halfShift
#print axioms projectiveLine_transpose_shift_not_inverse

end MillenniumHodgeFoundation
