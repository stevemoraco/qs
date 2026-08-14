import Mathlib

/-!
Finite integer shadow of `stevemoraco/RH#390`.

Formalized here only:
* self-intersection under a sequence of rational `(-1)` blowdowns is modeled by
  adding a sum of squares of intersection multiplicities;
* hence a surviving curve starting at self-intersection `-2` never ends below
  `-2`, in particular never at `-3`;
* changing the unique elliptic survivor from `-2` to `-1` costs total square
  increment exactly one.

Not formalized here:
resolution of surface singularities, the factorization through the minimal
resolution, Saito's simple-elliptic classification, the inference that the
Faenzi--Stipins double-root endpoint is `\widetilde E_7`, endpoint adjacency,
K3/triple-cover geometry, algebraic cycles, or the Hodge conjecture. No axiom
below carries any such conclusion.
-/

namespace Millennium.Hodge.R3Q1A7GraphABlowdownFiniteCore

def afterBlowdowns (start : ℤ) (qs : List ℤ) : ℤ :=
  start + (qs.map fun q => q^2).sum

theorem square_sum_nonnegative (qs : List ℤ) :
    0 ≤ (qs.map fun q => q^2).sum := by
  exact List.sum_nonneg (fun q hq => sq_nonneg q)

theorem minus_two_survivor_floor (qs : List ℤ) :
    (-2 : ℤ) ≤ afterBlowdowns (-2) qs := by
  simp only [afterBlowdowns]
  have h := square_sum_nonnegative qs
  omega

theorem minus_two_survivor_ne_minus_three (qs : List ℤ) :
    afterBlowdowns (-2) qs ≠ -3 := by
  have h := minus_two_survivor_floor qs
  omega

theorem elliptic_minus_two_to_minus_one_exact_increment
    (qs : List ℤ)
    (h : afterBlowdowns (-2) qs = -1) :
    (qs.map fun q => q^2).sum = 1 := by
  simp only [afterBlowdowns] at h
  omega

theorem no_second_nonzero_after_unit_increment
    (q : ℤ) (hq : q ≠ 0) :
    (1 : ℤ) < 1 + q^2 := by
  have hsq : 0 < q^2 := sq_pos_of_ne_zero hq
  omega

#check afterBlowdowns
#check square_sum_nonnegative
#check minus_two_survivor_floor
#check minus_two_survivor_ne_minus_three
#check elliptic_minus_two_to_minus_one_exact_increment
#check no_second_nonzero_after_unit_increment

#print axioms square_sum_nonnegative
#print axioms minus_two_survivor_floor
#print axioms minus_two_survivor_ne_minus_three
#print axioms elliptic_minus_two_to_minus_one_exact_increment
#print axioms no_second_nonzero_after_unit_increment

end Millennium.Hodge.R3Q1A7GraphABlowdownFiniteCore
