import Mathlib

/-!
# Positive Yu work forces positive nondegenerate mass

Finite weighted real algebra only. The central theorem is a sharp one-sided
threshold estimate: a positive weighted mean of a quantity bounded above by
`M` forces quantitative weight on the region where that quantity exceeds any
lower threshold `κ`.

For Yu's normalized angular work kernel the previous geometric branch proves
`|K| ≤ 1/2`. Applying this file to a nonnegative pointwise positive-work density
with `M = 1/2` converts a positive averaged work floor into positive profile
mass in a region where `K > κ`.

This file does **not** formalize Yu's PDE work functional, amplitude truncation,
Young-measure realization, tightness, recurrence, Navier--Stokes regularity, or
blow-up.
-/

open scoped BigOperators

noncomputable section

namespace NSYuPositiveWorkMass

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Total weight carried by points whose visible work is strictly above `κ`. -/
def visibleWeight (w k : ι → ℝ) (κ : ℝ) : ℝ :=
  ∑ i, if κ < k i then w i else 0

/-- A bounded positive mean forces a quantitative amount of visible weight.

No pointwise lower bound is assumed. The conclusion is the exact finite form
of

`(α-κ) totalWeight ≤ (M-κ) visibleWeight`.
-/
theorem bounded_mean_forces_visible_mass
    (w k : ι → ℝ) (κ α M : ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hkM : ∀ i, k i ≤ M)
    (hmean : α * (∑ i, w i) ≤ ∑ i, w i * k i) :
    (α - κ) * (∑ i, w i) ≤
      (M - κ) * visibleWeight w k κ := by
  have hpoint : ∀ i,
      w i * k i ≤
        κ * w i + (M - κ) * (if κ < k i then w i else 0) := by
    intro i
    by_cases hi : κ < k i
    · simp only [hi, if_true]
      have hmul := mul_le_mul_of_nonneg_left (hkM i) (hw i)
      nlinarith
    · have hik : k i ≤ κ := le_of_not_gt hi
      simp only [hi, if_false, mul_zero, add_zero]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hik (hw i)
  have hupper :
      (∑ i, w i * k i) ≤
        κ * (∑ i, w i) + (M - κ) * visibleWeight w k κ := by
    calc
      (∑ i, w i * k i) ≤
          ∑ i, (κ * w i + (M - κ) *
            (if κ < k i then w i else 0)) := by
        exact Finset.sum_le_sum (fun i _hi => hpoint i)
      _ = κ * (∑ i, w i) +
          (M - κ) * visibleWeight w k κ := by
        unfold visibleWeight
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  linarith

/-- If the mean threshold is strictly above `κ`, the total weight is positive,
and `κ < M`, then the visible region has strictly positive weight. -/
theorem positive_mean_forces_positive_visible_weight
    (w k : ι → ℝ) (κ α M : ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hkM : ∀ i, k i ≤ M)
    (hκM : κ < M)
    (hκα : κ < α)
    (hweight : 0 < ∑ i, w i)
    (hmean : α * (∑ i, w i) ≤ ∑ i, w i * k i) :
    0 < visibleWeight w k κ := by
  have hmass := bounded_mean_forces_visible_mass
    w k κ α M hw hkM hmean
  have hleft : 0 < (α - κ) * (∑ i, w i) :=
    mul_pos (sub_pos.mpr hκα) hweight
  by_contra hnot
  have hveryle : visibleWeight w k κ ≤ 0 := le_of_not_gt hnot
  have hright : (M - κ) * visibleWeight w k κ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hκM.le) hveryle
  linarith

/-- Probability-normalized `M = 1/2` form for Yu's sharp angular kernel bound.
For every `κ < 1/2`, a mean work floor `α` forces at least
`(α-κ)/(1/2-κ)` visible mass above `κ`. -/
theorem half_bounded_mean_forces_mass_fraction
    (w k : ι → ℝ) (κ α : ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hksup : ∀ i, k i ≤ (1 / 2 : ℝ))
    (hweight : (∑ i, w i) = 1)
    (hκhalf : κ < (1 / 2 : ℝ))
    (hmean : α * (∑ i, w i) ≤ ∑ i, w i * k i) :
    (α - κ) / ((1 / 2 : ℝ) - κ) ≤ visibleWeight w k κ := by
  have hmass := bounded_mean_forces_visible_mass
    w k κ α (1 / 2 : ℝ) hw hksup hmean
  rw [hweight, mul_one] at hmass
  apply (div_le_iff₀ (sub_pos.mpr hκhalf)).2
  simpa [mul_comm] using hmass

/-- Choosing `κ = α/2` yields a strictly positive explicit mass fraction when
`0 < α < 1`. -/
theorem half_bounded_mean_half_threshold
    (w k : ι → ℝ) (α : ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hksup : ∀ i, k i ≤ (1 / 2 : ℝ))
    (hweight : (∑ i, w i) = 1)
    (hα0 : 0 < α)
    (hα1 : α < 1)
    (hmean : α * (∑ i, w i) ≤ ∑ i, w i * k i) :
    0 < α / (1 - α) ∧
      α / (1 - α) ≤ visibleWeight w k (α / 2) := by
  constructor
  · exact div_pos hα0 (sub_pos.mpr hα1)
  · have hκhalf : α / 2 < (1 / 2 : ℝ) := by linarith
    have hmass := half_bounded_mean_forces_mass_fraction
      w k (α / 2) α hw hksup hweight hκhalf hmean
    have hden : 1 - α ≠ 0 := ne_of_gt (sub_pos.mpr hα1)
    have hhalfden : (1 / 2 : ℝ) - α / 2 ≠ 0 := by linarith
    have heq :
        (α - α / 2) / ((1 / 2 : ℝ) - α / 2) = α / (1 - α) := by
      field_simp [hden, hhalfden]
      ring
    simpa [heq] using hmass

/-- Positive average does not imply pointwise positivity everywhere: two equal
atoms with values `1/2` and `0` have average `1/4`, while one atom remains
completely work-invisible. -/
theorem positive_mean_not_pointwise_everywhere :
    (1 / 4 : ℝ) = (1 / 2 : ℝ) * (1 / 2 : ℝ) +
        (1 / 2 : ℝ) * 0 ∧
      ¬ (0 < (0 : ℝ)) := by
  norm_num

/-- The threshold coefficient is algebraically sharp for a two-level model:
visible mass `p` at height `M` and the remaining mass at exactly `κ` has mean
`κ + (M-κ)p`, saturating the estimate. -/
theorem two_level_threshold_bound_is_sharp
    (p κ M : ℝ) :
    (κ + (M - κ) * p - κ) = (M - κ) * p := by
  ring

#print axioms visibleWeight
#print axioms bounded_mean_forces_visible_mass
#print axioms positive_mean_forces_positive_visible_weight
#print axioms half_bounded_mean_forces_mass_fraction
#print axioms half_bounded_mean_half_threshold
#print axioms positive_mean_not_pointwise_everywhere
#print axioms two_level_threshold_bound_is_sharp

end NSYuPositiveWorkMass
