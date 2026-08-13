import Mathlib

/-!
# Marginal cubic flow cannot be a strict linear contraction near zero

Finite real-analysis core for the weak-coupling audit of arXiv:2606.19362.
It does not formalize Yang--Mills.  It records the elementary incompatibility
between a marginal beta-function map

  g ↦ g - β g^3 + R,   |R| ≤ c g^5

and a uniform linear contraction factor ρ < 1 arbitrarily close to g = 0.
-/

namespace YangMillsBraid

/-- If the cubic/quintic correction is smaller than the linear gap `1-ρ`,
then a marginal flow step has magnitude strictly larger than `ρ*g`.
Thus it cannot obey `|g'| ≤ ρ |g|` on every sufficiently small positive `g`
for any fixed `ρ < 1`. -/
theorem marginal_cubic_not_strict_linear_contraction
    (ρ β c g R : ℝ)
    (hρ0 : 0 ≤ ρ)
    (hg : 0 < g)
    (hsmall : β * g^2 + c * g^4 < 1 - ρ)
    (hR : |R| ≤ c * g^5) :
    ρ * g < |g - β * g^3 + R| := by
  have hs := mul_lt_mul_of_pos_right hsmall hg
  have hRlow : -(c * g^5) ≤ R := (abs_le.mp hR).1
  have hbase : ρ * g < g - β * g^3 - c * g^5 := by
    nlinarith
  have hstep : ρ * g < g - β * g^3 + R := by
    linarith
  have hnonneg : 0 ≤ ρ * g := mul_nonneg hρ0 (le_of_lt hg)
  have hpos : 0 < g - β * g^3 + R := lt_of_le_of_lt hnonneg hstep
  rw [abs_of_pos hpos]
  exact hstep

/-- Direct contradiction form: no bound `|g'| ≤ ρ*g` can coexist with the
small-correction hypotheses above. -/
theorem no_strict_contraction_bound_for_marginal_step
    (ρ β c g R : ℝ)
    (hρ0 : 0 ≤ ρ)
    (hg : 0 < g)
    (hsmall : β * g^2 + c * g^4 < 1 - ρ)
    (hR : |R| ≤ c * g^5) :
    ¬ |g - β * g^3 + R| ≤ ρ * g := by
  intro hcon
  have hgt := marginal_cubic_not_strict_linear_contraction
    ρ β c g R hρ0 hg hsmall hR
  linarith

end YangMillsBraid
