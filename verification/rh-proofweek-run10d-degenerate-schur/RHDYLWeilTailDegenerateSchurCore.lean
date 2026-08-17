import Mathlib

/-!
# Scalar degenerate Schur firewall for the DYL/Weil tail bridge

This file formalizes only the one-kernel-coordinate real shadow of the
semidefinite branch in the accompanying human note.

If the kernel quadratic coefficient vanishes but the cross coefficient does
not, the affine graph cost can be driven below every prescribed threshold.
If both vanish, the graph cost is constant, so the reserve is decided by the
remaining scalar Schur value.

This does NOT formalize complex Hermitian matrices, Moore--Penrose inverses,
inertia, Paley--Wiener interpolation, zeta zeros, Suzuki's forms, DYL, or RH.
-/

namespace RHDYLWeilTailDegenerateSchurCore

def tailCost (a b c r : ℝ) : ℝ :=
  a * r^2 + 2 * b * r + c

/-- If the kernel quadratic vanishes while the cross term is nonzero, the
affine graph cost can be pushed below every prescribed scalar level. -/
theorem zeroKernel_nonzeroCross_beatsAnyLevel
    (b c d : ℝ) (hb : b ≠ 0) :
    ∃ r : ℝ, tailCost 0 b c r < d := by
  let r : ℝ := (d - c - 1) / (2 * b)
  refine ⟨r, ?_⟩
  have h2b : (2 * b : ℝ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) hb
  have hmul : (2 * b) * r = d - c - 1 := by
    dsimp [r]
    field_simp [h2b] <;> ring
  rw [show tailCost 0 b c r = (2 * b) * r + c by simp [tailCost]]
  rw [hmul]
  linarith

/-- With zero kernel quadratic and zero cross term, the graph coefficient is
irrelevant: every graph has the same tail cost. -/
theorem zeroKernel_zeroCross_isConstant
    (c r : ℝ) :
    tailCost 0 0 c r = c := by
  simp [tailCost]

/-- In the compatible degenerate scalar branch, a strict Schur reserve is
exactly a negative full selected-block direction. -/
theorem zeroKernel_zeroCross_reserve
    (c d r : ℝ) (hreserve : c < d) :
    -d + tailCost 0 0 c r < 0 := by
  simp [tailCost]
  linarith

/-- The incompatible degenerate branch already gives a negative full
direction for any fixed selected-block budget. -/
theorem zeroKernel_nonzeroCross_makesFullNegative
    (b c d : ℝ) (hb : b ≠ 0) :
    ∃ r : ℝ, -d + tailCost 0 b c r < 0 := by
  obtain ⟨r, hr⟩ := zeroKernel_nonzeroCross_beatsAnyLevel b c d hb
  exact ⟨r, by linarith⟩

#print axioms zeroKernel_nonzeroCross_beatsAnyLevel
#print axioms zeroKernel_zeroCross_isConstant
#print axioms zeroKernel_zeroCross_reserve
#print axioms zeroKernel_nonzeroCross_makesFullNegative

end RHDYLWeilTailDegenerateSchurCore
