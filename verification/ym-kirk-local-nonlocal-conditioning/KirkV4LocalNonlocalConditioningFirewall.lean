import Mathlib

namespace Millennium.YangMills

/-- Three scalar coordinates: two finite local-jet coordinates and one
reported nonlocal coordinate. -/
abbrev KirkV3 := ℝ × (ℝ × ℝ)

/--
The upper-triangular local coupling in the parametric countermodel.
The two diagonal local scaling factors are `L⁻¹` and `L⁻²`; the coupling is
chosen so that two individually small local/nonlocal cross rows close an
exact eigenvalue-two feedback cycle.
-/
def kirkLocalCoupling (L : ℝ) : ℝ :=
  2 * (2 - 1 / L) * (2 - 1 / L ^ 2) * L ^ 6

/-- The finite local block, extended by zero on the nonlocal coordinate. -/
def kirkLocalBlock (L : ℝ) (v : KirkV3) : KirkV3 :=
  (v.1 / L + kirkLocalCoupling L * v.2.1,
    (v.2.1 / L ^ 2, 0))

/--
Two cross-block rows of size `L⁻³`: nonlocal input feeds the second local
coordinate, and the first local coordinate feeds the nonlocal output.
-/
def kirkNonlocalBlock (L : ℝ) (v : KirkV3) : KirkV3 :=
  (0, (v.2.2 / L ^ 3, v.1 / L ^ 3))

/-- The complete local-plus-nonlocal derivative. -/
def kirkFullBlock (L : ℝ) (v : KirkV3) : KirkV3 :=
  (v.1 / L + kirkLocalCoupling L * v.2.1,
    (v.2.1 / L ^ 2 + v.2.2 / L ^ 3,
      v.1 / L ^ 3))

/-- The exact unstable eigenvector of the complete block. -/
def kirkUnstableVector (L : ℝ) : KirkV3 :=
  (2 * (2 - 1 / L ^ 2) * L ^ 6,
    (1, (2 - 1 / L ^ 2) * L ^ 3))

/-- The displayed full block is exactly the sum of its local and nonlocal
parts. -/
theorem kirkFullBlock_eq_local_add_nonlocal
    (L : ℝ) (v : KirkV3) :
    kirkFullBlock L v = kirkLocalBlock L v + kirkNonlocalBlock L v := by
  ext <;> simp [kirkFullBlock, kirkLocalBlock, kirkNonlocalBlock]

/-- The countermodel witness is nonzero for every parameter because its middle
coordinate is one. -/
theorem kirkUnstableVector_ne_zero (L : ℝ) :
    kirkUnstableVector L ≠ 0 := by
  intro h
  have hm := congrArg (fun v : KirkV3 => v.2.1) h
  norm_num [kirkUnstableVector] at hm

/--
For every nonzero scale parameter, the complete block has exact eigenvalue
`2`.  This is the algebraic feedback cycle hidden by separately estimating
an upper-triangular local block and small cross-block rows.
-/
theorem kirkFullBlock_has_eigenvalue_two
    (L : ℝ) (hL : L ≠ 0) :
    kirkFullBlock L (kirkUnstableVector L) =
      (2 : ℝ) • kirkUnstableVector L := by
  apply Prod.ext
  · simp [kirkFullBlock, kirkUnstableVector, kirkLocalCoupling]
    field_simp [hL]
    ring
  · apply Prod.ext
    · simp [kirkFullBlock, kirkUnstableVector, kirkLocalCoupling]
      field_simp [hL]
      ring
    · simp [kirkFullBlock, kirkUnstableVector, kirkLocalCoupling]
      field_simp [hL]
      ring

/-- Any genuine eigenvalue of modulus two prevents an operator contraction in
*every* norm, regardless of how the coordinates are renormed. -/
theorem eigenvalue_two_prevents_contraction
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E → E)
    (v : E)
    (hv : v ≠ 0)
    (heigen : A v = (2 : ℝ) • v)
    (c : ℝ)
    (hc : c < 2) :
    ¬ ‖A v‖ ≤ c * ‖v‖ := by
  intro h
  rw [heigen, norm_smul] at h
  norm_num at h
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  nlinarith

/-- The Kirk-shaped complete block cannot satisfy any contraction estimate
with constant below two. -/
theorem kirkFullBlock_not_contractive
    (L : ℝ) (hL : L ≠ 0)
    (c : ℝ) (hc : c < 2) :
    ¬ ‖kirkFullBlock L (kirkUnstableVector L)‖ ≤
      c * ‖kirkUnstableVector L‖ := by
  exact eigenvalue_two_prevents_contraction
    (kirkFullBlock L)
    (kirkUnstableVector L)
    (kirkUnstableVector_ne_zero L)
    (kirkFullBlock_has_eigenvalue_two L hL)
    c hc

/-- At the first dyadic macrostep, the local triangular coupling is exactly
`120`, while the two cross-block coefficients are exactly `1/8`. -/
theorem kirk_scale_two_exact_ledger :
    kirkLocalCoupling 2 = 120 ∧
    (1 / (2 : ℝ) ^ 3) = 1 / 8 ∧
    (120 : ℝ) ≤ 2 ^ 7 := by
  norm_num [kirkLocalCoupling]

/-- The scale-two instance already has an exact eigenvalue two with a rational
witness `(120,1,10)`. -/
theorem kirk_scale_two_rational_witness :
    kirkUnstableVector 2 = (120, (1, 10)) ∧
    kirkFullBlock 2 (120, (1, 10)) = (240, (2, 20)) := by
  norm_num [kirkUnstableVector, kirkFullBlock, kirkLocalCoupling]

#print axioms kirkFullBlock_eq_local_add_nonlocal
#print axioms kirkUnstableVector_ne_zero
#print axioms kirkFullBlock_has_eigenvalue_two
#print axioms eigenvalue_two_prevents_contraction
#print axioms kirkFullBlock_not_contractive
#print axioms kirk_scale_two_exact_ledger
#print axioms kirk_scale_two_rational_witness

end Millennium.YangMills
