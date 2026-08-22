import Mathlib

/-!
# Yang--Mills master-correlation observability: finite core

Honesty status: this file formalizes only elementary ordered-field and finite-
sum statements used in the finite-horizon observability obstruction.

It does not formalize matrices, eigenvalues, trace-class operators, spectral
measures, semigroups, Osterwalder--Schrader reconstruction, gauge fields,
Yang--Mills, or the Clay statement.
-/

namespace MillenniumBraid
namespace YMObservabilityCapacityFinite

/-- Exact algebraic relative excess of a two-level hidden mode. -/
theorem hiddenExcessIdentity (a r : ℝ) :
    (1 - a) + a * r - 1 = a * (r - 1) := by
  ring

/-- A nonnegative hidden weight and amplification factor at least one give a
nonnegative relative excess. -/
theorem hiddenExcessNonnegative
    (a r : ℝ) (ha : 0 ≤ a) (hr : 1 ≤ r) :
    0 ≤ a * (r - 1) := by
  positivity

/-- Relative hidden excess increases with the amplification factor. -/
theorem hiddenExcessMonotone
    (a r s : ℝ) (ha : 0 ≤ a) (hrs : r ≤ s) :
    a * (r - 1) ≤ a * (s - 1) := by
  nlinarith

/-- If hidden overlap is at most the finite capacity `q/d`, then its relative
excess is bounded by `(q/d)(r-1)`. -/
theorem hiddenExcessLeCapacity
    (a q d r : ℝ)
    (ha : a ≤ q / d)
    (hr : 1 ≤ r) :
    a * (r - 1) ≤ (q / d) * (r - 1) := by
  exact mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hr)

/-- Scalar positive-kernel hidden-mass bound. -/
theorem hiddenMassBound
    (a A targetKernel lowKernel eps : ℝ)
    (hlow : 0 < lowKernel)
    (hupper : a * lowKernel ≤ A * targetKernel + eps) :
    a ≤ (A * targetKernel + eps) / lowKernel := by
  exact (le_div_iff₀ hlow).2 hupper

/-- A supplied positive observability floor contradicts an upper budget that
lies strictly below the amplified floor. -/
theorem observabilityFloorExcludesHidden
    (a eta r budget : ℝ)
    (hr : 0 ≤ r)
    (hfloor : eta ≤ a)
    (hupper : a * r ≤ budget)
    (hseparate : budget < eta * r) :
    False := by
  have hamp : eta * r ≤ a * r :=
    mul_le_mul_of_nonneg_right hfloor hr
  linarith

/-- Minimum-at-most-average for a nonempty finite coordinate family. -/
theorem existsCoordinateAtMostAverage
    {d : ℕ}
    (hd : 0 < d)
    (weight : Fin d → ℝ)
    (total : ℝ)
    (hsum : ∑ i, weight i = total) :
    ∃ i, weight i ≤ total / (d : ℝ) := by
  let avg : ℝ := total / (d : ℝ)
  have hdR : (d : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hd
  have hconst : ∑ _i : Fin d, avg = total := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, avg]
    field_simp
  have hle : ∑ i, weight i ≤ ∑ _i : Fin d, avg := by
    rw [hsum, hconst]
  have huniv : (Finset.univ : Finset (Fin d)).Nonempty := by
    exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hd)
  obtain ⟨i, _hi, hsmall⟩ :=
    Finset.exists_le_of_sum_le huniv hle
  exact ⟨i, hsmall⟩

/-- Rational growth-factor form of the breadth--time--dimension bound after the
small-overlap coordinate has been supplied. -/
theorem probeCapacityBound
    (overlap q d r : ℝ)
    (hoverlap : overlap ≤ q / d)
    (hr : 1 ≤ r) :
    overlap * (r - 1) ≤ (q / d) * (r - 1) := by
  exact hiddenExcessLeCapacity overlap q d r hoverlap hr

#print axioms hiddenExcessIdentity
#print axioms hiddenExcessNonnegative
#print axioms hiddenExcessMonotone
#print axioms hiddenExcessLeCapacity
#print axioms hiddenMassBound
#print axioms observabilityFloorExcludesHidden
#print axioms existsCoordinateAtMostAverage
#print axioms probeCapacityBound

end YMObservabilityCapacityFinite
end MillenniumBraid
