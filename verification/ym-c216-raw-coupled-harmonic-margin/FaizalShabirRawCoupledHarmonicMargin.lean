import Mathlib

/-!
# Faizal--Shabir raw coupled harmonic margin

Finite real-algebra firewall for the raw-coordinate AF/IR repair around
arXiv:2606.19362v1, Section 10.

The field-theoretic producer is external.  The intended asymptotic coupled
system has a marginal discrepancy with harmonic contraction and a stable
irrelevant discrepancy with a strict geometric contraction.  In raw
coordinates the stable `g^2` source contributes back to the marginal equation.
The finite scalar condition for a positive remaining harmonic margin is the
Schur-complement inequality

    L * A < c * (1 - q),

where `c/n` is the bare harmonic contraction, `q<1` is the stable contraction,
`A/sqrt(n)` feeds marginal discrepancy into the stable sector, and
`L/sqrt(n)` feeds the stable discrepancy back into the marginal sector.

This file does not formalize the Yang--Mills RG map, Banach/polymer norms,
AF/IR identification, Osterwalder--Schrader reconstruction, a mass gap, or a
Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirRawCoupledHarmonicMargin

/-- The effective harmonic margin is positive exactly when the stable feedback
Schur complement is smaller than the bare harmonic contraction. -/
theorem effective_margin_pos_iff
    (c q A L : ℝ)
    (hq : q < 1) :
    0 < c - (L * A) / (1 - q) ↔ L * A < c * (1 - q) := by
  have hden : 0 < 1 - q := sub_pos.mpr hq
  constructor
  · intro h
    have h' : (L * A) / (1 - q) < c := by linarith
    exact (div_lt_iff₀ hden).mp h'
  · intro h
    have h' : (L * A) / (1 - q) < c := (div_lt_iff₀ hden).2 h
    linarith

/-- Source-normalized scalar shadow of the raw-coordinate feedback criterion.
After the AF normalization `g_n ~ (2 beta n)^(-1/2)`, the pure cubic map has
harmonic coefficient `3/2`, while a stable-source / marginal-feedback product
contributes the scalar debt `c1*c3 / (beta*(1-q))`. -/
theorem three_halves_feedback_margin_iff
    (beta q c1 c3 : ℝ)
    (hbeta : 0 < beta)
    (hq : q < 1) :
    0 < (3 / 2 : ℝ) - (c1 * c3) / (beta * (1 - q)) ↔
      2 * c1 * c3 < 3 * beta * (1 - q) := by
  have hqden : 0 < 1 - q := sub_pos.mpr hq
  have hden : 0 < beta * (1 - q) := mul_pos hbeta hqden
  constructor
  · intro h
    have h' : (c1 * c3) / (beta * (1 - q)) < (3 / 2 : ℝ) := by
      linarith
    have hm : c1 * c3 < (3 / 2 : ℝ) * (beta * (1 - q)) :=
      (div_lt_iff₀ hden).mp h'
    nlinarith
  · intro h
    have hm : c1 * c3 < (3 / 2 : ℝ) * (beta * (1 - q)) := by
      nlinarith
    have h' : (c1 * c3) / (beta * (1 - q)) < (3 / 2 : ℝ) :=
      (div_lt_iff₀ hden).2 hm
    linarith

/-- A strict source-normalized feedback margin leaves a positive polynomial
AF/IR decay exponent available at the finite scalar level. -/
theorem positive_decay_exponent_exists
    (beta q c1 c3 : ℝ)
    (hbeta : 0 < beta)
    (hq : q < 1)
    (hmargin : 2 * c1 * c3 < 3 * beta * (1 - q)) :
    ∃ p : ℝ,
      0 < p ∧
      p < (3 / 2 : ℝ) - (c1 * c3) / (beta * (1 - q)) := by
  have hpos :
      0 < (3 / 2 : ℝ) - (c1 * c3) / (beta * (1 - q)) :=
    (three_halves_feedback_margin_iff beta q c1 c3 hbeta hq).2 hmargin
  refine ⟨((3 / 2 : ℝ) - (c1 * c3) / (beta * (1 - q))) / 2, ?_, ?_⟩
  · linarith
  · linarith

#print axioms effective_margin_pos_iff
#print axioms three_halves_feedback_margin_iff
#print axioms positive_decay_exponent_exists

end Millennium.YangMills.FaizalShabirRawCoupledHarmonicMargin
