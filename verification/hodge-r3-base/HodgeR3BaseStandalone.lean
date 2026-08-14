import Mathlib

/-!
Standalone public verifier for the finite polynomial core used in
`stevemoraco/RH#314` and `stevemoraco/RH#315`.

It verifies only explicit commutative-ring polynomial identities and elementary
integer ledgers. No K3 geometry, Mordell-Weil theorem, Groebner basis,
weighted blow-up, conductor theorem, or Hodge conclusion is encoded.
-/

namespace HodgeR3BaseStandalone

variable {R : Type*} [CommRing R]

def cubicDisc (c3 c2 c1 c0 : R) : R :=
  c2 ^ 2 * c1 ^ 2
    - 4 * c3 * c1 ^ 3
    - 4 * c2 ^ 3 * c0
    - 27 * c3 ^ 2 * c0 ^ 2
    + 18 * c3 * c2 * c1 * c0

def residualPhi (A B a b alpha : R) : R :=
  4 * A ^ 3 * alpha ^ 6
    - 24 * A ^ 2 * a * b * alpha ^ 4
    - A ^ 2 * b ^ 4 * alpha ^ 2
    + 18 * A * B * b ^ 2 * alpha ^ 4
    + 30 * A * a ^ 2 * b ^ 2 * alpha ^ 2
    + 4 * A * a * b ^ 5
    + 27 * B ^ 2 * alpha ^ 6
    - 54 * B * a ^ 2 * alpha ^ 4
    - 36 * B * a * b ^ 3 * alpha ^ 2
    - 4 * B * b ^ 6
    + 27 * a ^ 4 * alpha ^ 2
    + 4 * a ^ 3 * b ^ 3

theorem cubic_discriminant_factor
    (A B a b alpha : R) :
    cubicDisc
        (alpha ^ 2)
        (-(b ^ 2))
        (alpha ^ 2 * A - 2 * a * b)
        (alpha ^ 2 * B - a ^ 2)
      = -(alpha ^ 2) * residualPhi A B a b alpha := by
  simp only [cubicDisc, residualPhi]
  ring

theorem alpha_zero_boundary_factor (A B a b : R) :
    residualPhi A B a b 0 =
      4 * b ^ 3 * (a ^ 3 + A * a * b ^ 2 - B * b ^ 3) := by
  simp only [residualPhi]
  ring

def maxCancel (a b u : R) : Prop :=
  27 * a * u + 4 * b ^ 3 = 0

theorem weight_ten_after_max_cancel
    (A a b u : R) (h : maxCancel a b u) :
    2 * A * a * b ^ 2 * (15 * a * u + 2 * b ^ 3) =
      3 * A * a ^ 2 * b ^ 2 * u := by
  have hdiff :
      2 * A * a * b ^ 2 * (15 * a * u + 2 * b ^ 3)
          - 3 * A * a ^ 2 * b ^ 2 * u = 0 := by
    calc
      2 * A * a * b ^ 2 * (15 * a * u + 2 * b ^ 3)
          - 3 * A * a ^ 2 * b ^ 2 * u =
          A * a * b ^ 2 * (27 * a * u + 4 * b ^ 3) := by ring
      _ = 0 := by rw [h]; ring
  exact sub_eq_zero.mp hdiff

theorem conductor_degree_ledger :
    (24 : ℤ) = 2 * 9 + 6 := by
  norm_num

theorem parameter_degree_ledger :
    (78 : ℤ) = 6 * 13 := by
  norm_num

theorem normal_length_ledger :
    (14 : ℕ) * 2 = 28 := by
  norm_num

theorem normal_multiplicity_ledger :
    (2 : ℕ) * 3 ^ 3 = 54 := by
  norm_num

theorem power_surface_degree_ledger :
    (3 : ℕ) ^ 2 = 9 := by
  norm_num

theorem square_degree_boundary_deficit :
    (8 : ℕ) < 9 := by
  norm_num

#print axioms cubic_discriminant_factor
#print axioms alpha_zero_boundary_factor
#print axioms weight_ten_after_max_cancel
#print axioms conductor_degree_ledger
#print axioms parameter_degree_ledger
#print axioms normal_length_ledger
#print axioms normal_multiplicity_ledger
#print axioms power_surface_degree_ledger
#print axioms square_degree_boundary_deficit

end HodgeR3BaseStandalone
