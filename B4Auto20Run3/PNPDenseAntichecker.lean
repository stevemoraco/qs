import Mathlib

namespace B4Auto20Run3

/-- BANKER: the uniform false-positive error inequality for a one-sided support
set is exactly the cardinality lower bound after clearing the negative-universe
denominator. `N`, `m`, and `A` stand for universe, positive-set, and acceptance
cardinalities, represented here in `ℝ`. -/
theorem pnp_uniform_error_cardinality_iff
    (N m A eps : ℝ) (hNm : m < N) :
    (A - m) / (N - m) > eps ↔
      A > eps * (N - m) + m := by
  have hden : 0 < N - m := sub_pos.mpr hNm
  constructor
  · intro h
    have h' : eps * (N - m) < A - m :=
      (lt_div_iff₀ hden).mp h
    linarith
  · intro h
    apply (lt_div_iff₀ hden).2
    linarith

/-- CLEANER: a genuinely positive uniform false-positive lower bound forces a
one-sided support acceptance set to contain strictly more points than the
positive set itself, so an exact decider is excluded. -/
theorem pnp_positive_uniform_error_forces_extra_acceptance
    (N m A eps : ℝ) (hNm : m < N) (heps : 0 < eps)
    (herror : (A - m) / (N - m) > eps) :
    m < A := by
  have hcard := (pnp_uniform_error_cardinality_iff N m A eps hNm).mp herror
  have hden : 0 < N - m := sub_pos.mpr hNm
  have hprod : 0 < eps * (N - m) := mul_pos heps hden
  linarith

/-- CRITIC: replacing the strict positive-error premise by a non-strict
`≥ 0` premise does not exclude an exact support set: its false-positive error is
exactly zero. -/
theorem pnp_nonstrict_zero_error_allows_exact_decider :
    (0 : ℝ) ≤ ((5 : ℝ) - 5) / (10 - 5) := by
  norm_num

#print axioms B4Auto20Run3.pnp_uniform_error_cardinality_iff
#print axioms B4Auto20Run3.pnp_positive_uniform_error_forces_extra_acceptance
#print axioms B4Auto20Run3.pnp_nonstrict_zero_error_allows_exact_decider

end B4Auto20Run3
