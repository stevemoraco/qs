import Mathlib

/-!
# Yang--Mills C484 finite relative-gap / physical-unit core

These theorems formalize only finite real-algebra consequences of a relative
Dirichlet-form comparison. They do not formalize transfer operators, lattice
gauge theory, Balaban activities, Osterwalder--Schrader reconstruction, or the
Yang--Mills Millennium problem.
-/

namespace Millennium.YangMills.C484

/-- A relative gap fraction gives the affine eigenvalue bound
`lambdaActual <= 1-c+c*lambdaIdeal`. -/
theorem relative_gap_fraction_eigenvalue_bound
    (c lambdaIdeal lambdaActual : ℝ)
    (hgap : c * (1 - lambdaIdeal) ≤ 1 - lambdaActual) :
    lambdaActual ≤ 1 - c + c * lambdaIdeal := by
  linarith

/-- Multiplying the affine eigenvalue recurrence by a positive physical
normalization exposes the additive relative-loss debt. -/
theorem physical_normalization_exposes_relative_loss
    (m aNext c lambdaIdeal lambdaActual : ℝ)
    (hrec : lambdaActual ≤ 1 - c + c * lambdaIdeal) :
    Real.exp (m * aNext) * lambdaActual ≤
      c * (Real.exp (m * aNext) * lambdaIdeal) +
        Real.exp (m * aNext) * (1 - c) := by
  have hexp : 0 ≤ Real.exp (m * aNext) := (Real.exp_pos _).le
  calc
    Real.exp (m * aNext) * lambdaActual ≤
        Real.exp (m * aNext) * (1 - c + c * lambdaIdeal) :=
      mul_le_mul_of_nonneg_left hrec hexp
    _ = c * (Real.exp (m * aNext) * lambdaIdeal) +
        Real.exp (m * aNext) * (1 - c) := by ring

/-- One exact relative physical-tube step. -/
theorem relative_physical_tube_step
    (c qIdeal rPow delta r qActual : ℝ)
    (hc : 0 ≤ c)
    (hactual : qActual ≤ c * qIdeal + delta)
    (hideal : qIdeal ≤ rPow)
    (hdelta : delta ≤ r - c * rPow) :
    qActual ≤ r := by
  have hmul : c * qIdeal ≤ c * rPow :=
    mul_le_mul_of_nonneg_left hideal hc
  linarith

/-- The geometric relative-loss algebra used by the scalar countermodel. -/
theorem geometric_relative_loss_exact_recurrence (k : ℕ) :
    let loss : ℝ := (1 / 2 : ℝ) ^ k
    let c : ℝ := 1 - loss
    loss = 1 - c + c * 0 := by
  simp

/-- Any fixed nonnegative dimensionless logarithmic loss can be made smaller
than a prescribed positive physical rate by choosing a sufficiently large
physical spacing. -/
theorem fixed_dimensionless_loss_beaten_by_large_spacing
    (loss target : ℝ)
    (hloss : 0 ≤ loss)
    (htarget : 0 < target) :
    ∃ spacing : ℝ, 0 < spacing ∧ loss < target * spacing := by
  let spacing : ℝ := (loss + 1) / target
  have hloss1 : 0 < loss + 1 := by linarith
  have hspacing : 0 < spacing := div_pos hloss1 htarget
  refine ⟨spacing, hspacing, ?_⟩
  dsimp [spacing]
  have htarget0 : target ≠ 0 := ne_of_gt htarget
  calc
    loss < loss + 1 := by linarith
    _ = target * ((loss + 1) / target) := by field_simp

/-- A positive dimensionless multiplicative reserve is not itself a lower
bound in physical units; the physical spacing still enters. -/
theorem positive_reserve_does_not_fix_physical_rate
    (reserve loss target : ℝ)
    (hreserve : 0 < reserve)
    (hloss : 0 ≤ loss)
    (htarget : 0 < target) :
    ∃ spacing : ℝ,
      0 < spacing ∧ 0 < reserve ∧ loss < target * spacing := by
  obtain ⟨spacing, hspacing, hrate⟩ :=
    fixed_dimensionless_loss_beaten_by_large_spacing loss target hloss htarget
  exact ⟨spacing, hspacing, hreserve, hrate⟩

#print axioms relative_gap_fraction_eigenvalue_bound
#print axioms physical_normalization_exposes_relative_loss
#print axioms relative_physical_tube_step
#print axioms geometric_relative_loss_exact_recurrence
#print axioms fixed_dimensionless_loss_beaten_by_large_spacing
#print axioms positive_reserve_does_not_fix_physical_rate

end Millennium.YangMills.C484
