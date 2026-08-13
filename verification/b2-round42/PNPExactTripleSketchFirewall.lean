import Mathlib

/-!
# PNP exact triple-sketch finite firewalls

This file formalizes only finite arithmetic and Fourier-table shadows used in
the exact `ceil(2d/3)` repetition-sketch theorem. It does not formalize random
matrices, Fourier inversion on finite groups, Boolean circuits, RepSAT, SAT,
NP, or `P ≠ NP`.
-/

namespace MillenniumBraid
namespace B2Round42PNPTriple

/-- Exact matrix support of the triple construction: two ones per complete
triple and one deterministic check per leftover coordinate. -/
def tripleSupport (d : ℕ) : ℕ := 2 * (d / 3) + d % 3

/-- The triple support is exactly the integer ceiling of `2d/3`. -/
theorem tripleSupport_eq_ceiling (d : ℕ) :
    tripleSupport d = (2 * d + 2) / 3 := by
  omega

/-- The exact integer lower-bound form. -/
theorem tripleSupport_is_least_integer_above_two_thirds (d T : ℕ)
    (h : 2 * d ≤ 3 * T) :
    tripleSupport d ≤ T := by
  rw [tripleSupport_eq_ceiling]
  omega

/-- The support itself meets the cross-multiplied lower bound. -/
theorem tripleSupport_meets_two_thirds (d : ℕ) :
    2 * d ≤ 3 * tripleSupport d := by
  unfold tripleSupport
  omega

/-- No more than five output rows are needed: three random parity rows and at
most two deterministic leftover rows. -/
theorem output_row_cap (d : ℕ) : 3 + d % 3 ≤ 5 := by
  omega

/-- Fourier coefficients for a triple intersected in one coordinate. -/
def phiOne : Fin 4 → ℚ
  | 0 => 1
  | 1 => 5 / 9
  | 2 => 1 / 9
  | 3 => -1 / 3

/-- Fourier coefficients for a triple intersected in two coordinates. -/
def phiTwo : Fin 4 → ℚ
  | 0 => 1
  | 1 => 1 / 9
  | 2 => -1 / 3
  | 3 => -1 / 3

/-- Fourier coefficients for a triple intersected in all three coordinates. -/
def phiThree : Fin 4 → ℚ
  | 0 => 1
  | 1 => -1 / 3
  | 2 => -1 / 3
  | 3 => 1

/-- The exact Fourier-inversion miss expression from counts of one-, two-, and
three-coordinate triple intersections. -/
noncomputable def exactMiss (a b c : ℕ) : ℚ :=
  (1
    + 3 * (5 / 9 : ℚ) ^ a * (1 / 9 : ℚ) ^ b * (-1 / 3 : ℚ) ^ c
    + 3 * (1 / 9 : ℚ) ^ a * (-1 / 3 : ℚ) ^ (b + c)
    + (-1 / 3 : ℚ) ^ (a + b)) / 8

/-- A single one-coordinate intersection attains error exactly one third. -/
theorem exactMiss_one_single : exactMiss 1 0 0 = (1 : ℚ) / 3 := by
  norm_num [exactMiss]

/-- A single two-coordinate intersection is rejected perfectly. -/
theorem exactMiss_two_single : exactMiss 0 1 0 = 0 := by
  norm_num [exactMiss]

/-- A single full-triple intersection is rejected perfectly. -/
theorem exactMiss_three_single : exactMiss 0 0 1 = 0 := by
  norm_num [exactMiss]

/-- Two full-triple intersections attain the one-third boundary. -/
theorem exactMiss_two_full_triples : exactMiss 0 0 2 = (1 : ℚ) / 3 := by
  norm_num [exactMiss]

/-- Representative strict mixed case. -/
theorem exactMiss_one_and_full_strict : exactMiss 1 0 1 < (1 : ℚ) / 3 := by
  norm_num [exactMiss]

/-- Representative strict two-coordinate multi-block case. -/
theorem exactMiss_two_two_intersections_strict :
    exactMiss 0 2 0 < (1 : ℚ) / 3 := by
  norm_num [exactMiss]

/-- The coarse `a=0,b>=1` case closes whenever the three nontrivial Fourier
terms have absolute bounds `1/3`, `1`, and `1/3`. -/
theorem coarse_three_term_bound
    {A B C : ℚ}
    (hA : A ≤ 1 / 3) (hB : B ≤ 1) (hC : C ≤ 1 / 3) :
    (1 + A + B + C) / 8 ≤ (1 : ℚ) / 3 := by
  linarith

/-- The strict `a>=1` nonexceptional case closes from one term below one and
two terms bounded by one third. -/
theorem strict_three_term_bound
    {A B C : ℚ}
    (hA : A < 1) (hB : B ≤ 1 / 3) (hC : C ≤ 1 / 3) :
    (1 + A + B + C) / 8 < (1 : ℚ) / 3 := by
  linarith

/-- Exact lifted gate-budget regrouping with at most five representative
appearances per source bit. -/
theorem exact_lift_gate_budget
    (source d m : ℕ) :
    source + tripleSupport d + 5 * m + 5
      = source + (2 * d + 2) / 3 + 5 * m + 5 := by
  rw [tripleSupport_eq_ceiling]

#print axioms tripleSupport_eq_ceiling
#print axioms tripleSupport_is_least_integer_above_two_thirds
#print axioms tripleSupport_meets_two_thirds
#print axioms output_row_cap
#print axioms exactMiss_one_single
#print axioms exactMiss_two_single
#print axioms exactMiss_three_single
#print axioms exactMiss_two_full_triples
#print axioms exactMiss_one_and_full_strict
#print axioms exactMiss_two_two_intersections_strict
#print axioms coarse_three_term_bound
#print axioms strict_three_term_bound
#print axioms exact_lift_gate_budget

end B2Round42PNPTriple
end MillenniumBraid
