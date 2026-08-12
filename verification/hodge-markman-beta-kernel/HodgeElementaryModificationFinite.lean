import Mathlib

namespace HodgeElementaryModificationFinite

/-- The explicit universal parameter choice used in the elementary
modification satisfies the exact cubic Chern-character balance. -/
theorem explicit_parameter_balance
    (n d : ℚ) :
    let M := n ^ 2 + 4 * d
    let e := 2 * M
    let f := 2 * M
    let r := 96 * M
    24 * e * f = r * (n ^ 2 + 4 * d) := by
  dsimp
  ring

/-- The parameter balance converts the divisor cubic term minus the
complete-intersection curve term into the desired proportional secant
coefficient. -/
theorem proportional_chern_coefficient
    {n d e f r : ℚ}
    (hbalance : 24 * e * f = r * (n ^ 2 + 4 * d)) :
    r * n ^ 3 / 24 - n * e * f = -(r * n * d) / 6 := by
  have hpoly : r * n ^ 3 - 24 * n * e * f = -4 * r * n * d := by
    nlinarith [hbalance]
  linarith

/-- Under the norm-one relation, the first cubic eigencoefficient of
`d A^3 - q B^3` is the first coefficient of `d A - q B`. -/
theorem first_norm_one_cubic_coefficient
    {a b d q : ℚ}
    (hab : a * b = 1) :
    d * a ^ 2 * b - q * b ^ 2 * a = d * a - q * b := by
  calc
    d * a ^ 2 * b - q * b ^ 2 * a = (a * b) * (d * a - q * b) := by ring
    _ = d * a - q * b := by rw [hab]; ring

/-- Under the norm-one relation, the second cubic eigencoefficient has the
same reduction. -/
theorem second_norm_one_cubic_coefficient
    {a b d q : ℚ}
    (hab : a * b = 1) :
    d * a * b ^ 2 - q * b * a ^ 2 = d * b - q * a := by
  calc
    d * a * b ^ 2 - q * b * a ^ 2 = (a * b) * (d * b - q * a) := by ring
    _ = d * b - q * a := by rw [hab]; ring

/-- Scalar form of the complete-intersection ray identity after the two
norm-one coefficient reductions. -/
theorem complete_intersection_cube_ray
    (u v : ℚ) :
    u ^ 2 * v = (u * v) * u ∧
      u * v ^ 2 = (u * v) * v := by
  constructor <;> ring

/-- The rank-r curve bundle and the rank-r finite gluing quotient have equal
point-class contribution when their Euler characteristic and length agree. -/
theorem point_term_cancels
    {chiV r z : ℚ}
    (hchi : chiV = r * z) :
    chiV - r * z = 0 := by
  linarith

/-- The proportional constituent cubic term and the correcting curve cubic
term cancel in the A-direction. -/
theorem final_A_cubic_cancels
    (N d : ℚ) :
    -(N * d) / 6 + N * d / 6 = 0 := by
  ring

/-- The remaining B-cubic coefficient is exactly the target mixed coefficient.
-/
theorem final_B_cubic_coefficient
    (N q : ℚ) :
    -(N * q) / 6 = N * (-(q / 6)) := by
  ring

#print axioms explicit_parameter_balance
#print axioms proportional_chern_coefficient
#print axioms first_norm_one_cubic_coefficient
#print axioms second_norm_one_cubic_coefficient
#print axioms complete_intersection_cube_ray
#print axioms point_term_cancels
#print axioms final_A_cubic_cancels
#print axioms final_B_cubic_coefficient

end HodgeElementaryModificationFinite
