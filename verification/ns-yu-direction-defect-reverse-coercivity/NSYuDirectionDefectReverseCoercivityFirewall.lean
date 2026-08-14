import Mathlib

/-!
# Yu direction-defect reverse-coercivity firewall

Finite real algebra only.  The scalar `yuKernelCoupling` is the contraction
factor appearing after contracting Yu's near-field strain kernel against a
local direction `x`, a displacement direction `z`, and a remote direction `y`:

  (x · z) * ((x × z) · (y - x)).

The explicit orthogonal configuration below has a strictly positive direction
defect but zero kernel coupling.  Hence Yu's one-way estimate from positive
near-field work to a pairwise direction defect cannot be inverted by a
universal positive coercivity constant.

This file does not formalize Yu's PDE theorem, filtered vorticity, singular
solutions, Navier--Stokes regularity, or blow-up.
-/

namespace NSYuDirectionDefectReverseCoercivityFirewall

/-- Squared Euclidean direction defect in three scalar coordinates. -/
def directionDefectSq
    (x1 x2 x3 y1 y2 y3 : ℝ) : ℝ :=
  (y1 - x1)^2 + (y2 - x2)^2 + (y3 - x3)^2

/-- Scalar shadow of
`(x · z) * ((x × z) · (y - x))`. -/
def yuKernelCoupling
    (x1 x2 x3 z1 z2 z3 y1 y2 y3 : ℝ) : ℝ :=
  let dotxz := x1*z1 + x2*z2 + x3*z3
  let cross1 := x2*z3 - x3*z2
  let cross2 := x3*z1 - x1*z3
  let cross3 := x1*z2 - x2*z1
  dotxz *
    (cross1*(y1-x1) + cross2*(y2-x2) + cross3*(y3-x3))

/-- For `x=e₁` and `y=e₃`, the direction defect is nonzero. -/
theorem explicit_direction_defect_sq :
    directionDefectSq 1 0 0 0 0 1 = 2 := by
  norm_num [directionDefectSq]

/-- For `x=e₁`, displacement `z=e₂`, and remote direction `y=e₃`,
the exact geometric coupling vanishes because `x · z = 0`. -/
theorem explicit_yu_kernel_coupling_zero :
    yuKernelCoupling 1 0 0 0 1 0 0 0 1 = 0 := by
  norm_num [yuKernelCoupling]

/-- A strictly positive direction defect can therefore be completely invisible
to the exact near-field geometric work factor. -/
theorem positive_direction_defect_with_zero_coupling :
    0 < directionDefectSq 1 0 0 0 0 1 ∧
      yuKernelCoupling 1 0 0 0 1 0 0 0 1 = 0 := by
  constructor
  · rw [explicit_direction_defect_sq]
    norm_num
  · exact explicit_yu_kernel_coupling_zero

/-- No universal positive reverse-coercivity constant can turn this geometric
work factor back into the full direction defect. -/
theorem no_positive_reverse_coercivity
    (c : ℝ) (hc : 0 < c) :
    ¬ c * directionDefectSq 1 0 0 0 0 1 ≤
      |yuKernelCoupling 1 0 0 0 1 0 0 0 1| := by
  rw [explicit_direction_defect_sq, explicit_yu_kernel_coupling_zero]
  simp only [abs_zero]
  nlinarith

/-- In particular, zero geometric work does not force zero direction defect. -/
theorem zero_coupling_does_not_force_zero_defect :
    ¬ (yuKernelCoupling 1 0 0 0 1 0 0 0 1 = 0 →
       directionDefectSq 1 0 0 0 0 1 = 0) := by
  intro h
  have hzero := h explicit_yu_kernel_coupling_zero
  rw [explicit_direction_defect_sq] at hzero
  norm_num at hzero

#print axioms explicit_direction_defect_sq
#print axioms explicit_yu_kernel_coupling_zero
#print axioms positive_direction_defect_with_zero_coupling
#print axioms no_positive_reverse_coercivity
#print axioms zero_coupling_does_not_force_zero_defect

end NSYuDirectionDefectReverseCoercivityFirewall
