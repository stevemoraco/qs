import Mathlib

/-!
# Dimensional-transmutation normalization firewall

This file isolates the finite algebra behind a load-bearing scale-identification
step in regulator-to-continuum Yang--Mills arguments.

Suppose `ell` is an operational matching length and `lambdaLead` is a scale
fixed only at leading asymptotic order, normalized so that

    ell * lambdaLead = 1.

If the physically/canonically normalized transmutation scale differs by a
multiplicative remainder `r`,

    lambdaPhysical = lambdaLead * r,

then the normalized matching scale is *exactly* that remainder:

    ell * lambdaPhysical = r.

Thus no regulator-uniform two-sided comparison between `ell` and the physical
transmutation scale can follow until `r` itself has a regulator-uniform
positive lower and finite upper bound.  In logarithmic variables a remainder
`R` becomes `r = exp R`; an error only controlled at logarithmic size can
therefore encode polynomial multiplicative drift.

This is only a finite scalar firewall.  It does not formalize the Yang--Mills
beta function, a particular renormalization scheme, asymptotic freedom,
reflection positivity, Osterwalder--Schrader reconstruction, or a continuum
limit.
-/

namespace Millennium.YangMills

/-- A multiplicative normalization remainder survives unchanged in the
matching-length times transmutation-scale product. -/
theorem normalizedScale_eq_remainder
    {ell lambdaLead r : ℝ}
    (hmatch : ell * lambdaLead = 1) :
    ell * (lambdaLead * r) = r := by
  calc
    ell * (lambdaLead * r) = (ell * lambdaLead) * r := by ring
    _ = r := by rw [hmatch]; ring

/-- Consequently a two-sided normalized physical-scale window is equivalent
to the same two-sided window on the multiplicative remainder. -/
theorem normalizedScale_window_iff_remainder_window
    {ell lambdaLead r c C : ℝ}
    (hmatch : ell * lambdaLead = 1) :
    (c ≤ ell * (lambdaLead * r) ∧ ell * (lambdaLead * r) ≤ C) ↔
      (c ≤ r ∧ r ≤ C) := by
  rw [normalizedScale_eq_remainder hmatch]

/-- Leading-order matching alone cannot supply any prescribed positive lower
normalized-scale bound: an unconstrained positive multiplicative remainder
can undershoot it. -/
theorem leadingMatch_allows_arbitrary_undershoot
    {ell lambdaLead c : ℝ}
    (hmatch : ell * lambdaLead = 1)
    (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ ell * (lambdaLead * r) < c := by
  refine ⟨c / 2, ?_, ?_⟩
  · linarith
  · rw [normalizedScale_eq_remainder hmatch]
    linarith

/-- Leading-order matching alone also cannot supply any prescribed finite
upper normalized-scale bound: an unconstrained positive multiplicative
remainder can overshoot it. -/
theorem leadingMatch_allows_arbitrary_overshoot
    {ell lambdaLead C : ℝ}
    (hmatch : ell * lambdaLead = 1)
    (hC : 0 ≤ C) :
    ∃ r : ℝ, 0 < r ∧ C < ell * (lambdaLead * r) := by
  refine ⟨C + 1, ?_, ?_⟩
  · linarith
  · rw [normalizedScale_eq_remainder hmatch]
    linarith

/-- A bounded positive remainder immediately transfers to a bounded positive
normalized transmutation scale.  This is the finite algebraic form of the
missing normalization theorem. -/
theorem normalizedScale_window_of_remainder_window
    {ell lambdaLead r c C : ℝ}
    (hmatch : ell * lambdaLead = 1)
    (hlower : c ≤ r)
    (hupper : r ≤ C) :
    c ≤ ell * (lambdaLead * r) ∧ ell * (lambdaLead * r) ≤ C := by
  rw [normalizedScale_eq_remainder hmatch]
  exact ⟨hlower, hupper⟩

#print axioms normalizedScale_eq_remainder
#print axioms normalizedScale_window_iff_remainder_window
#print axioms leadingMatch_allows_arbitrary_undershoot
#print axioms leadingMatch_allows_arbitrary_overshoot
#print axioms normalizedScale_window_of_remainder_window

end Millennium.YangMills
