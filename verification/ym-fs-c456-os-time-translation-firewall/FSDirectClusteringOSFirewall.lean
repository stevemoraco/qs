import Mathlib

/-!
# Faizal–Shabir direct-clustering OS firewall

This file formalizes only the rational two-state algebra used in the C456
source audit. It does not formalize probability measures, reflection
positivity, Osterwalder--Schrader reconstruction, Yang--Mills, or a Clay
Millennium theorem.
-/

namespace Millennium.YangMills.FSC456

abbrev State := ℚ × ℚ

/-- Reversible two-state transfer with nontrivial eigenvalue `1/2`. -/
def transfer (x : State) : State :=
  ((3 * x.1 + x.2) / 4, (x.1 + 3 * x.2) / 4)

/-- Centered eigenvector. -/
def centered : State := (1, -1)

/-- Rational dot-product shadow of the slice `L²` inner product. -/
def dot (x y : State) : ℚ := x.1 * y.1 + x.2 * y.2

/-- One positive-time step contracts the centered mode by exactly one half. -/
theorem transfer_centered :
    transfer centered = ((1 / 2 : ℚ), (-1 / 2 : ℚ)) := by
  norm_num [transfer, centered]

/-- Two positive-time steps contract the centered mode by exactly one quarter. -/
theorem transfer_twice_centered :
    transfer (transfer centered) = ((1 / 4 : ℚ), (-1 / 4 : ℚ)) := by
  norm_num [transfer, centered]

/-- The shifted centered norm is exactly one quarter of the original norm. -/
theorem shifted_norm_ratio :
    dot (transfer centered) (transfer centered) =
      (1 / 4 : ℚ) * dot centered centered := by
  norm_num [dot, transfer, centered]

/-- Hence the nontrivial positive-time transfer is not an isometry. -/
theorem positive_time_shift_not_isometry :
    dot (transfer centered) (transfer centered) ≠ dot centered centered := by
  norm_num [dot, transfer, centered]

/-- The vacuum eigenvalue `0` belongs to the half-open interval `[0,1)`. -/
theorem vacuum_belongs_to_closed_left_interval :
    (0 : ℚ) ∈ Set.Ico 0 1 := by
  constructor <;> norm_num

/-- The vacuum does not belong to the corrected open interval `(0,1)`. -/
theorem vacuum_not_in_open_zero_interval :
    (0 : ℚ) ∉ Set.Ioo 0 1 := by
  simp

#print axioms transfer_centered
#print axioms transfer_twice_centered
#print axioms shifted_norm_ratio
#print axioms positive_time_shift_not_isometry
#print axioms vacuum_belongs_to_closed_left_interval
#print axioms vacuum_not_in_open_zero_interval

end Millennium.YangMills.FSC456
