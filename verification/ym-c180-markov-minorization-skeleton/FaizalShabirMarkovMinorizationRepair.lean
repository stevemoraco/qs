import Mathlib

/-!
# Faizal--Shabir Markov-minorization repair firewall

Finite kernel/form algebra for a possible repair of the Yang--Mills transfer-gap
bridge.  The source paper has symmetric Markov transfer kernels and detailed
balance at finite lattice spacing.  If an *analytic Yang--Mills theorem* supplies
a pointwise minorization of the actual reversible edge kernel by the ideal one,
then the corresponding Dirichlet form inherits the same multiplicative lower
bound.  This converts a likelihood-ratio/minorization theorem into exactly the
relative-form spectral currency isolated by the hostile audit.

Nothing here proves such a minorization for Yang--Mills, proves regulator or
volume uniformity, identifies AF and IR, constructs a continuum OS theory, or
proves a mass gap / Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirMarkovMinorizationRepair

open scoped BigOperators

/-- Finite doubled edge-energy sum.  The conventional factor `1/2` is omitted;
it cancels in every comparison below. -/
def edgeEnergy {α : Type*} [DecidableEq α]
    (S : Finset α) (w : α → α → ℝ) (f : α → ℝ) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ S, w x y * (f x - f y) ^ 2

/-- Pointwise nonnegative edge-kernel minorization passes to the finite
Dirichlet/edge-energy sum. -/
theorem edgeEnergy_minorization
    {α : Type*} [DecidableEq α]
    (S : Finset α) (wIdeal wActual : α → α → ℝ) (f : α → ℝ) (c : ℝ)
    (hminor : ∀ x ∈ S, ∀ y ∈ S, c * wIdeal x y ≤ wActual x y) :
    c * edgeEnergy S wIdeal f ≤ edgeEnergy S wActual f := by
  unfold edgeEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  exact mul_le_mul_of_nonneg_right (hminor x hx y hy) (sq_nonneg (f x - f y))

/-- A multiplicative lower comparison of the actual Dirichlet form gives the
relative upper-error estimate needed by the spectral consumer. -/
theorem minorization_gives_relative_form_loss
    (idealForm actualForm c : ℝ)
    (hcomp : c * idealForm ≤ actualForm) :
    idealForm - actualForm ≤ (1 - c) * idealForm := by
  linarith

/-- Log-likelihood minorization `exp(-δ)` gives the corresponding relative-form
loss coefficient `1-exp(-δ)`. -/
theorem log_minorization_gives_relative_form_loss
    (idealForm actualForm δ : ℝ)
    (hcomp : Real.exp (-δ) * idealForm ≤ actualForm) :
    idealForm - actualForm ≤ (1 - Real.exp (-δ)) * idealForm := by
  linarith

/-- A nonnegative log distortion gives a retained minorization factor in
`(0,1]`. -/
theorem log_minorization_factor_range
    (δ : ℝ) (hδ : 0 ≤ δ) :
    0 < Real.exp (-δ) ∧ Real.exp (-δ) ≤ 1 := by
  constructor
  · exact Real.exp_pos _
  · have hneg : -δ ≤ 0 := by linarith
    simpa using (Real.exp_le_exp.mpr hneg)

/-- If the ideal Dirichlet/spectral edge is at least `gap`, then an
`exp(-δ)` minorization retains at least the same factor of that edge. -/
theorem log_minorization_preserves_gap_floor
    (gap idealGap actualGap δ : ℝ)
    (hgap : gap ≤ idealGap)
    (hactual : Real.exp (-δ) * idealGap ≤ actualGap) :
    Real.exp (-δ) * gap ≤ actualGap := by
  have hscale : Real.exp (-δ) * gap ≤ Real.exp (-δ) * idealGap :=
    mul_le_mul_of_nonneg_left hgap (le_of_lt (Real.exp_pos _))
  exact hscale.trans hactual

/-- Once the entire accumulated log-distortion budget has been compressed to a
finite real number `totalDistortion`, a positive initial gap remains positive
under the retained factor `exp(-totalDistortion)`. -/
theorem finite_log_distortion_keeps_positive_gap
    (gap actualGap totalDistortion : ℝ)
    (hgap : 0 < gap)
    (hactual : Real.exp (-totalDistortion) * gap ≤ actualGap) :
    0 < actualGap := by
  have hpositive : 0 < Real.exp (-totalDistortion) * gap :=
    mul_pos (Real.exp_pos _) hgap
  exact hpositive.trans_le hactual

#print axioms edgeEnergy_minorization
#print axioms minorization_gives_relative_form_loss
#print axioms log_minorization_gives_relative_form_loss
#print axioms log_minorization_factor_range
#print axioms log_minorization_preserves_gap_floor
#print axioms finite_log_distortion_keeps_positive_gap

end Millennium.YangMills.FaizalShabirMarkovMinorizationRepair
