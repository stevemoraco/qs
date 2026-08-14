import Mathlib

noncomputable section

/-!
# Navier--Stokes: sharp logarithmic sequence exponent gate for Yu closure

Runlong Yu's annular Carleson theorem (arXiv:2606.27560v1, Theorem 8.7)
closes the unweighted reassigned far field if the annular sequence `A` and the
local-enstrophy sequence `Q` lie in conjugate sequence spaces `ell^p` and
`ell^q`.

For the model logarithmic decays

  A_j ~ (j+1)^(-alpha),   Q_j ~ (j+1)^(-beta),

p-series summability asks for `alpha*p > 1` and `beta*q > 1`.  The finite
algebra below proves the sharp compatibility threshold for those inequalities:
there exist positive conjugate exponents with both strict gains exactly when
`alpha + beta > 1` (assuming alpha,beta>0).

The convenient canonical choice is

  p = (alpha+beta)/alpha,  q = (alpha+beta)/beta,

for which both weighted exponents equal `alpha+beta`.

This file formalizes only the scalar exponent arithmetic.  It does not prove
Yu's analytic theorem, any decay estimate for an actual Navier--Stokes solution,
or regularity/blow-up.
-/

namespace NSYuLogarithmicSequenceThreshold

theorem canonical_conjugate_exponents
    {alpha beta : ℝ} (ha : 0 < alpha) (hb : 0 < beta) :
    let p := (alpha + beta) / alpha
    let q := (alpha + beta) / beta
    0 < p ∧ 0 < q ∧ 1 < p ∧ 1 < q ∧
      1 / p + 1 / q = 1 ∧
      alpha * p = alpha + beta ∧
      beta * q = alpha + beta := by
  dsimp
  have ha0 : alpha ≠ 0 := ne_of_gt ha
  have hb0 : beta ≠ 0 := ne_of_gt hb
  have hs : 0 < alpha + beta := add_pos ha hb
  have hs0 : alpha + beta ≠ 0 := ne_of_gt hs
  have hp : 0 < (alpha + beta) / alpha := div_pos hs ha
  have hq : 0 < (alpha + beta) / beta := div_pos hs hb
  have hp1 : 1 < (alpha + beta) / alpha := by
    apply (lt_div_iff₀ ha).2
    linarith
  have hq1 : 1 < (alpha + beta) / beta := by
    apply (lt_div_iff₀ hb).2
    linarith
  refine ⟨hp, hq, hp1, hq1, ?_, ?_, ?_⟩
  · field_simp [ha0, hb0, hs0]
  · field_simp [ha0]
  · field_simp [hb0]

theorem total_gain_constructs_summable_exponents
    {alpha beta : ℝ} (ha : 0 < alpha) (hb : 0 < beta)
    (hs : 1 < alpha + beta) :
    let p := (alpha + beta) / alpha
    let q := (alpha + beta) / beta
    0 < p ∧ 0 < q ∧ 1 < p ∧ 1 < q ∧
      1 / p + 1 / q = 1 ∧
      1 < alpha * p ∧ 1 < beta * q := by
  dsimp
  rcases canonical_conjugate_exponents ha hb with
    ⟨hp, hq, hp1, hq1, hconj, halpha, hbeta⟩
  exact ⟨hp, hq, hp1, hq1, hconj,
    by simpa [halpha] using hs,
    by simpa [hbeta] using hs⟩

theorem summable_conjugate_exponents_force_total_gain
    {alpha beta p q : ℝ}
    (hp : 0 < p) (hq : 0 < q)
    (hconj : 1 / p + 1 / q = 1)
    (halpha : 1 < alpha * p)
    (hbeta : 1 < beta * q) :
    1 < alpha + beta := by
  have ha : 1 / p < alpha := by
    apply (div_lt_iff₀ hp).2
    simpa [mul_comm] using halpha
  have hb : 1 / q < beta := by
    apply (div_lt_iff₀ hq).2
    simpa [mul_comm] using hbeta
  linarith

theorem total_log_gain_iff_conjugate_summability_window
    {alpha beta : ℝ} (ha : 0 < alpha) (hb : 0 < beta) :
    1 < alpha + beta ↔
      ∃ p q : ℝ,
        0 < p ∧ 0 < q ∧ 1 < p ∧ 1 < q ∧
        1 / p + 1 / q = 1 ∧
        1 < alpha * p ∧ 1 < beta * q := by
  constructor
  · intro hs
    let p := (alpha + beta) / alpha
    let q := (alpha + beta) / beta
    have h := total_gain_constructs_summable_exponents ha hb hs
    dsimp at h
    exact ⟨p, q, h⟩
  · rintro ⟨p, q, hp, hq, _hp1, _hq1, hconj, halpha, hbeta⟩
    exact summable_conjugate_exponents_force_total_gain hp hq hconj halpha hbeta

#print axioms canonical_conjugate_exponents
#print axioms total_gain_constructs_summable_exponents
#print axioms summable_conjugate_exponents_force_total_gain
#print axioms total_log_gain_iff_conjugate_summability_window

end NSYuLogarithmicSequenceThreshold
