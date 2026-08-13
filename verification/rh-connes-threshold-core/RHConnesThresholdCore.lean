import Mathlib

/-!
# Connes threshold-inertia finite core

This file formalizes only the finite real-algebra and inertia bookkeeping in
`stevemoraco/RH#176`.

It does **not** formalize the truncated Weil operator, compact resolvents,
spectral calculus, the spectral projection theorem, Fourier integration,
Connes's candidate convergence theorem, Hurwitz/Rouche, Xi, zeta, or RH.
-/

namespace RHConnesThresholdCore

/-- Finite inertia ledger: numbers of negative, zero, and positive directions. -/
structure Inertia where
  neg : ℕ
  zero : ℕ
  pos : ℕ
  deriving DecidableEq, Repr

/-- Inertia is additive under an orthogonal direct sum. -/
def Inertia.directSum (a b : Inertia) : Inertia where
  neg := a.neg + b.neg
  zero := a.zero + b.zero
  pos := a.pos + b.pos

/-- If the shifted even block has exactly one negative direction and no zero,
and the shifted odd block is positive definite, then the complete parity sum
has exactly one negative direction and no zero.  Interpreting inertia as an
eigenvalue count is an external spectral theorem. -/
theorem parity_inertia_unique_negative
    {even odd : Inertia}
    (heNeg : even.neg = 1)
    (heZero : even.zero = 0)
    (hoNeg : odd.neg = 0)
    (hoZero : odd.zero = 0) :
    (Inertia.directSum even odd).neg = 1 ∧
      (Inertia.directSum even odd).zero = 0 := by
  simp [Inertia.directSum, heNeg, heZero, hoNeg, hoZero]

/-- Scalar residual-to-distance firewall in squared form.

`d*w ≤ r` abstracts the spectral complement estimate
`(t-mu)||w|| ≤ residual`, while `dist² ≤ 2w²` abstracts the elementary
phase-adjusted conversion from complementary mass to eigenvector distance.
-/
theorem residual_over_threshold_distance_sq
    {d r w dist : ℝ}
    (hd : 0 < d)
    (hw : 0 ≤ w)
    (hres : d * w ≤ r)
    (hdist : dist ^ 2 ≤ 2 * w ^ 2) :
    dist ^ 2 ≤ 2 * (r / d) ^ 2 := by
  have hr : 0 ≤ r := by
    nlinarith
  have hq : 0 ≤ r / d := div_nonneg hr (le_of_lt hd)
  have hwq : w ≤ r / d := by
    apply (le_div_iff₀ hd).2
    nlinarith
  have hprod : 0 ≤ (r / d - w) * (r / d + w) :=
    mul_nonneg (sub_nonneg.mpr hwq) (add_nonneg hq hw)
  have hsquares : w ^ 2 ≤ (r / d) ^ 2 := by
    nlinarith
  nlinarith

/-- Once a spectral theorem supplies an upper bound for the exact ground-state
distance, a nonnegative strip-amplification factor preserves the error budget. -/
theorem strip_budget_of_threshold_bound
    {amplification dist thresholdBound epsilon : ℝ}
    (hamp : 0 ≤ amplification)
    (hdist : dist ≤ thresholdBound)
    (hbudget : amplification * thresholdBound ≤ epsilon) :
    amplification * dist ≤ epsilon := by
  exact le_trans (mul_le_mul_of_nonneg_left hdist hamp) hbudget

/-- Schur safety margin: if the compressed second eigenvalue exceeds the
worst complementary correction, the corrected margin remains positive. -/
theorem schur_margin_positive
    {lambda₂ kappa delta : ℝ}
    (hdelta : 0 < delta)
    (hmargin : kappa ^ 2 / delta < lambda₂) :
    0 < lambda₂ - kappa ^ 2 / delta := by
  exact sub_pos.mpr hmargin

/-- The strict substrip condition `a < 1/2` makes the exponent left after an
`O(c^(-1/4))` candidate error strictly negative. -/
theorem quarter_rate_beats_closed_substrip
    {a : ℝ} (ha : a < 1 / 2) :
    a / 2 - 1 / 4 < 0 := by
  linarith

#print axioms parity_inertia_unique_negative
#print axioms residual_over_threshold_distance_sq
#print axioms strip_budget_of_threshold_bound
#print axioms schur_margin_positive
#print axioms quarter_rate_beats_closed_substrip

end RHConnesThresholdCore
