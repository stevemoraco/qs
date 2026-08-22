import Mathlib

/-!
# Rank-one parity safety finite core

This file formalizes only the pointwise real-algebra core of
`stevemoraco/RH`'s rank-one parity safety theorem.

It does **not** formalize quadratic-form domains, negative index, min--max,
compact resolvents, the truncated Weil operator, Fourier bases, the pole
functional, Xi, zeta, or RH.
-/

namespace RHRankOneParitySafetyCore

/-- Adding a nonnegative rank-one term cannot turn a nonnegative base value
into a negative value. -/
theorem positive_rank_one_preserves_nonnegative
    {base tau coupling : ℝ}
    (hbase : 0 ≤ base)
    (htau : 0 ≤ tau) :
    0 ≤ base + tau * coupling ^ 2 := by
  exact add_nonneg hbase (mul_nonneg htau (sq_nonneg coupling))

/-- Contrapositive form: if the positively updated value is negative, then
its pole-free base value was already negative.  This is the pointwise input
behind the statement that a positive update cannot increase negative index. -/
theorem positive_rank_one_negative_implies_base_negative
    {base tau coupling : ℝ}
    (htau : 0 ≤ tau)
    (hfull : base + tau * coupling ^ 2 < 0) :
    base < 0 := by
  have hcorr : 0 ≤ tau * coupling ^ 2 :=
    mul_nonneg htau (sq_nonneg coupling)
  linarith

/-- Generic negative-set inclusion for a pointwise nonnegative correction. -/
theorem negative_set_mono_of_nonnegative_correction
    {α : Type*}
    {base correction full : α → ℝ}
    (hfull : ∀ x, full x = base x + correction x)
    (hcorr : ∀ x, 0 ≤ correction x) :
    {x | full x < 0} ⊆ {x | base x < 0} := by
  intro x hx
  change full x < 0 at hx
  change base x < 0
  rw [hfull x] at hx
  linarith [hcorr x]

/-- Abstract scalar odd-sector margin.

`base ≥ m*normSq` is pole-free coercivity, `ellSq ≤ M*normSq` is a dual-norm
bound for the pole functional, and `tau*M < m` is the strict safety margin.
-/
theorem negative_rank_one_safe
    {base m normSq tau ellSq M : ℝ}
    (hnorm : 0 < normSq)
    (htau : 0 ≤ tau)
    (hbase : m * normSq ≤ base)
    (hell : ellSq ≤ M * normSq)
    (hmargin : tau * M < m) :
    0 < base - tau * ellSq := by
  have hupdate : tau * ellSq ≤ tau * (M * normSq) :=
    mul_le_mul_of_nonneg_left hell htau
  have hstrict : tau * M * normSq < m * normSq :=
    mul_lt_mul_of_pos_right hmargin hnorm
  have hstrict' : tau * (M * normSq) < m * normSq := by
    calc
      tau * (M * normSq) = tau * M * normSq := by ring
      _ < m * normSq := hstrict
  calc
    0 < m * normSq - tau * (M * normSq) := sub_pos.mpr hstrict'
    _ ≤ base - tau * ellSq := sub_le_sub hbase hupdate

/-- Cauchy--Schwarz-specialized form of the odd-sector safety gate. -/
theorem negative_rank_one_safe_of_cauchy
    {base m normXsq tau innerSq normWsq : ℝ}
    (hnormX : 0 < normXsq)
    (htau : 0 ≤ tau)
    (hbase : m * normXsq ≤ base)
    (hcauchy : innerSq ≤ normWsq * normXsq)
    (hmargin : tau * normWsq < m) :
    0 < base - tau * innerSq := by
  exact negative_rank_one_safe
    hnormX htau hbase hcauchy hmargin

/-- Uniform margin form: a base lower bound and a pole correction upper bound
combine into an explicit positive lower bound. -/
theorem explicit_rank_one_lower_bound
    {base m normSq tau ellSq M : ℝ}
    (htau : 0 ≤ tau)
    (hbase : m * normSq ≤ base)
    (hell : ellSq ≤ M * normSq) :
    (m - tau * M) * normSq ≤ base - tau * ellSq := by
  have hupdate : tau * ellSq ≤ tau * (M * normSq) :=
    mul_le_mul_of_nonneg_left hell htau
  calc
    (m - tau * M) * normSq
        = m * normSq - tau * (M * normSq) := by ring
    _ ≤ base - tau * ellSq := sub_le_sub hbase hupdate

#print axioms positive_rank_one_preserves_nonnegative
#print axioms positive_rank_one_negative_implies_base_negative
#print axioms negative_set_mono_of_nonnegative_correction
#print axioms negative_rank_one_safe
#print axioms negative_rank_one_safe_of_cauchy
#print axioms explicit_rank_one_lower_bound

end RHRankOneParitySafetyCore
