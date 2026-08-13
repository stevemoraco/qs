import Mathlib

/-!
# BSD floor-cancellation and filtered determinant firewall

This file formalizes finite arithmetic and a scalar upper-triangular determinant
identity only.  It does not formalize DVRs, module length, determinant functors,
Selmer complexes, regulators, Tate--Shafarevich groups, or BSD.
-/

namespace MillenniumBraid
namespace B2Round41BSD

/-- Minimal signed cancellation: the global floor can be hit although neither
component hits its own floor. -/
theorem signed_floor_cancellation_counterexample :
    ((-1 : ℤ) + 1 = 0 + 0) ∧
      ((-1 : ℤ) ≠ 0) ∧ ((1 : ℤ) ≠ 0) := by
  norm_num

/-- A finite sum of natural-number excesses vanishes exactly when every excess
vanishes. -/
theorem natural_excess_sum_zero_iff
    {ι : Type*} [Fintype ι] (e : ι → ℕ) :
    (∑ i, e i = 0) ↔ ∀ i, e i = 0 := by
  constructor
  · intro h i
    have hle : e i ≤ ∑ j, e j := by
      exact Finset.single_le_sum
        (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)
    omega
  · intro h
    simp [h]

/-- Scalar determinant of a two-by-two matrix. -/
def det2 {R : Type*} [CommRing R] (a b c d : R) : R :=
  a * d - b * c

/-- The off-diagonal extension entry is invisible to an upper-triangular
scalar determinant. -/
theorem upper_triangular_det
    {R : Type*} [CommRing R] (a u d : R) :
    det2 a u 0 d = a * d := by
  simp [det2]

/-- Additive length and valuation contributions regroup into additive defects. -/
theorem additive_defect_regroup
    (length₁ length₂ valuation₁ valuation₂ : ℤ) :
    (length₁ + length₂) + (valuation₁ + valuation₂) =
      (length₁ + valuation₁) + (length₂ + valuation₂) := by
  ring

#print axioms signed_floor_cancellation_counterexample
#print axioms natural_excess_sum_zero_iff
#print axioms upper_triangular_det
#print axioms additive_defect_regroup

end B2Round41BSD
end MillenniumBraid
