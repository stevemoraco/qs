import Mathlib

/-!
# PNP RepSAT sparse dual-hash arithmetic firewall

This file formalizes only the scalar conditioning/error calculation and the
finite gate-budget arithmetic used in the round-41 RepSAT audit.  It does not
formalize probability spaces, Chebyshev's inequality, repetition codes,
Boolean circuits, SAT, NP, or P versus NP.
-/

namespace MillenniumBraid
namespace B2Round41PNPRepSAT

/-- If a conditioning event has probability at least `15/16` and the joint
zero-parity event has probability at most `1/2`, then the conditioned
zero-parity probability is at most `8/15`.  The hypothesis `p*q ≤ 1/2` is the
cross-multiplied conditional-probability identity. -/
theorem conditioned_single_row_bound
    {p q : ℝ}
    (hp : (15 : ℝ) / 16 ≤ p)
    (hq : 0 ≤ q)
    (hjoint : p * q ≤ (1 : ℝ) / 2) :
    q ≤ (8 : ℝ) / 15 := by
  have hscaled : ((15 : ℝ) / 16) * q ≤ p * q :=
    mul_le_mul_of_nonneg_right hp hq
  nlinarith

/-- Two independent rows, each with conditioned zero-parity probability at
most `8/15`, have joint miss probability at most `64/225`. -/
theorem two_independent_rows_bound
    {q₁ q₂ : ℝ}
    (hq₂0 : 0 ≤ q₂)
    (hq₁ : q₁ ≤ (8 : ℝ) / 15)
    (hq₂ : q₂ ≤ (8 : ℝ) / 15) :
    q₁ * q₂ ≤ (64 : ℝ) / 225 := by
  calc
    q₁ * q₂ ≤ ((8 : ℝ) / 15) * q₂ :=
      mul_le_mul_of_nonneg_right hq₁ hq₂0
    _ ≤ ((8 : ℝ) / 15) * ((8 : ℝ) / 15) :=
      mul_le_mul_of_nonneg_left hq₂ (by norm_num)
    _ = (64 : ℝ) / 225 := by norm_num

/-- The explicit two-row miss probability lies strictly below one third. -/
theorem sixty_four_over_225_lt_one_third :
    (64 : ℝ) / 225 < (1 : ℝ) / 3 := by
  norm_num

/-- Combined conditioned-row firewall: two independent rows meet the standard
pointwise error threshold. -/
theorem conditioned_two_row_error_below_third
    {p₁ p₂ q₁ q₂ : ℝ}
    (hp₁ : (15 : ℝ) / 16 ≤ p₁)
    (hp₂ : (15 : ℝ) / 16 ≤ p₂)
    (hq₁0 : 0 ≤ q₁) (hq₂0 : 0 ≤ q₂)
    (hj₁ : p₁ * q₁ ≤ (1 : ℝ) / 2)
    (hj₂ : p₂ * q₂ ≤ (1 : ℝ) / 2) :
    q₁ * q₂ < (1 : ℝ) / 3 := by
  have h₁ := conditioned_single_row_bound hp₁ hq₁0 hj₁
  have h₂ := conditioned_single_row_bound hp₂ hq₂0 hj₂
  exact lt_of_le_of_lt
    (two_independent_rows_bound hq₂0 h₁ h₂)
    sixty_four_over_225_lt_one_third

/-- If twice the row support cap is bounded by `d + 4*r + 2`, then two raw
parity trees, `m` possible representative inputs per row, a source circuit of
size `s`, and two final gates fit the displayed near-`N` budget. -/
theorem sparse_hash_gate_budget
    {d m t r s : ℕ}
    (hcap : 2 * t ≤ d + 4 * r + 2) :
    s + 2 * t + 2 * m + 2 ≤
      s + (d + m) + m + 4 * r + 4 := by
  omega

/-- The elementary collapse-sensitive bookkeeping after writing `N=d+m`. -/
theorem ambient_budget_rewrite
    (d m s r : ℕ) :
    s + (d + m) + m + 4 * r + 4 =
      s + d + 2 * m + 4 * r + 4 := by
  omega

#print axioms conditioned_single_row_bound
#print axioms two_independent_rows_bound
#print axioms sixty_four_over_225_lt_one_third
#print axioms conditioned_two_row_error_below_third
#print axioms sparse_hash_gate_budget
#print axioms ambient_budget_rewrite

end B2Round41PNPRepSAT
end MillenniumBraid
