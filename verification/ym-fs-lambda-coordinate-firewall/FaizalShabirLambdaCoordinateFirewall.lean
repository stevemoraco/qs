import Mathlib

/-!
# Faizal--Shabir AF/IR transmutation-coordinate firewall

Finite scalar algebra behind a load-bearing warning for the weak-coupling
identification step. Two squared-coupling trajectories can become very close
while retaining a nonzero constant offset in inverse squared coupling, the
coordinate that carries the integration constant of the one-loop flow.

This file does not formalize Yang--Mills, renormalization, Lambda_YM,
Osterwalder--Schrader reconstruction, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirLambdaCoordinateFirewall

/-- Two reciprocal affine squared-coupling coordinates differ by an explicitly
quadratically small rational term. -/
theorem reciprocal_affine_difference
    (x c d : ℝ)
    (hxc : x + c ≠ 0)
    (hxd : x + d ≠ 0) :
    1 / (x + c) - 1 / (x + d) =
      (d - c) / ((x + c) * (x + d)) := by
  field_simp
  ring

/-- Inverting the same two squared-coupling coordinates recovers the constant
offset exactly. -/
theorem inverse_reciprocal_offset
    (x c d : ℝ)
    (hxc : x + c ≠ 0)
    (hxd : x + d ≠ 0) :
    1 / (1 / (x + c)) - 1 / (1 / (x + d)) = c - d := by
  field_simp
  ring

/-- Concrete one-unit-offset family: the raw squared couplings differ by a
product-denominator term while the inverse squared couplings remain separated
by exactly one unit. -/
theorem one_unit_transmutation_offset
    (x : ℝ)
    (hx1 : x + 1 ≠ 0)
    (hx2 : x + 2 ≠ 0) :
    (1 / (x + 1) - 1 / (x + 2) =
      1 / ((x + 1) * (x + 2))) ∧
    (1 / (1 / (x + 1)) - 1 / (1 / (x + 2)) = -1) := by
  constructor
  · simpa using reciprocal_affine_difference x 1 2 hx1 hx2
  · simpa using inverse_reciprocal_offset x 1 2 hx1 hx2

/-- Equality of the inverse-squared-coupling coordinate forces equality of the
affine integration constants in this model. -/
theorem inverse_coordinate_identifies_offset
    (x c d : ℝ)
    (hxc : x + c ≠ 0)
    (hxd : x + d ≠ 0)
    (hmatch : 1 / (1 / (x + c)) = 1 / (1 / (x + d))) :
    c = d := by
  have hoff := inverse_reciprocal_offset x c d hxc hxd
  rw [hmatch] at hoff
  linarith

#print axioms reciprocal_affine_difference
#print axioms inverse_reciprocal_offset
#print axioms one_unit_transmutation_offset
#print axioms inverse_coordinate_identifies_offset

end Millennium.YangMills.FaizalShabirLambdaCoordinateFirewall
