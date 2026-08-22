import Mathlib

/-!
# Hodge r=2 deck-extension finite core

Finite intersection/arithmetic shadow of the geometric theorem in
`stevemoraco/RH#313`.  This file does not formalize double covers, eigenspaces,
K3 surfaces, transported involutions, ramification, or the Hodge conjecture.
-/

namespace HodgeR2DeckLowLayersFinite

/-- Intersection form on `F_4` for classes `a*s+b*f`. -/
def f4Intersection (a b c d : ℤ) : ℤ :=
  -4 * a * c + a * d + b * c

/-- For `D_n=s+n f` and `K=-2s-6f`, the anti-invariant twist
`D_n+K=-s+(n-6)f` has fibre degree `-1`, independently of `n`. -/
theorem antiInvariantTwist_fibre_degree (n : ℤ) :
    f4Intersection (-1) (n - 6) 0 1 = -1 := by
  simp [f4Intersection]

/-- `D_n=s+n f` has ruling degree one. -/
theorem targetSection_fibre_degree (n : ℤ) :
    f4Intersection 1 n 0 1 = 1 := by
  simp [f4Intersection]

/-- `D_n=s+n f` meets the negative section in degree `n-4`. -/
theorem targetSection_negativeSection_degree (n : ℤ) :
    f4Intersection 1 n 1 0 = n - 4 := by
  simp [f4Intersection]
  ring

/-- If four distinct fixed points on a general source ruling must land in
`D_n ∩ s`, then the numerical intersection budget forces `n ≥ 8`. -/
theorem four_fixed_points_force_n_ge_eight
    (n : ℤ) (hfour : 4 ≤ n - 4) :
    8 ≤ n := by
  omega

/-- Consequently every integer height `4 ≤ n < 8` has too little negative-
section intersection budget for four distinct fixed points. -/
theorem low_height_has_fewer_than_four_negative_intersections
    (n : ℤ) (h4 : 4 ≤ n) (h8 : n < 8) :
    n - 4 < 4 := by
  omega

/-- For `L_n=2R+n e` with `R^2=-2`, `R.e=1`, `e^2=0`, the square is `4n-8`. -/
theorem r2_square_formula (n : ℤ) :
    4 * (-2) + 4 * n = 4 * n - 8 := by
  ring

/-- The four low `r=2` heights correspond exactly to squares 8,12,16,20. -/
theorem low_r2_square_values :
    (4 * (4 : ℤ) - 8 = 8) ∧
    (4 * (5 : ℤ) - 8 = 12) ∧
    (4 * (6 : ℤ) - 8 = 16) ∧
    (4 * (7 : ℤ) - 8 = 20) := by
  norm_num

/-- Integer exhaustion of the low-height range. -/
theorem low_r2_height_exhaustion
    (n : ℤ) (h4 : 4 ≤ n) (h8 : n < 8) :
    n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by
  omega

/-- The first odd numerical U candidate `3R+6e` has square 18. -/
theorem first_odd_r3_square :
    (-2 : ℤ) * 3^2 + 2 * 3 * 6 = 18 := by
  norm_num

/-- The first unresolved even `r=2` height after `n≤7` has square 24. -/
theorem first_remaining_r2_square :
    4 * (8 : ℤ) - 8 = 24 := by
  norm_num

#print axioms antiInvariantTwist_fibre_degree
#print axioms targetSection_fibre_degree
#print axioms targetSection_negativeSection_degree
#print axioms four_fixed_points_force_n_ge_eight
#print axioms low_height_has_fewer_than_four_negative_intersections
#print axioms r2_square_formula
#print axioms low_r2_square_values
#print axioms low_r2_height_exhaustion
#print axioms first_odd_r3_square
#print axioms first_remaining_r2_square

end HodgeR2DeckLowLayersFinite
