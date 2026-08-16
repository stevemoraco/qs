import Mathlib

namespace Millennium.YangMills

/-!
# Pre-differentiated source-margin admission

Finite scalar companion to the source-analyticity audit around Kirk v4
Corollary 8.12.

A strict source-free rooted/KP margin does not by itself produce a common
complex source ball. A sufficient quantitative input is a zero-order source
row which vanishes linearly with the source radius. The theorems below isolate
only the elementary margin arithmetic after such a row has been proved.

This file does not formalize Kirk's local-source activities, polymer/BKAR
bounds, matching expansion, Schwinger functions, Osterwalder--Schrader
reconstruction, a Yang--Mills mass gap, or a Clay theorem.
-/

/-- If the source-free row has strict margin below one, a source perturbation
bounded by `L * rho` is admitted whenever twice its worst-case rooted cost fits
inside the remaining margin. -/
theorem strict_root_margin_absorbs_source
    (Ctree eta sigma L rho etaSrc : ℝ)
    (hC : 0 ≤ Ctree)
    (hbase : Ctree * eta ≤ sigma)
    (hsigma : sigma < 1)
    (hsrc : etaSrc ≤ L * rho)
    (hsmall : 2 * Ctree * L * rho ≤ 1 - sigma) :
    Ctree * (eta + etaSrc) < 1 := by
  have hsrc' : Ctree * etaSrc ≤ Ctree * (L * rho) :=
    mul_le_mul_of_nonneg_left hsrc hC
  have hbudget : Ctree * (L * rho) ≤ (1 - sigma) / 2 := by
    nlinarith [hsmall]
  have hsum :
      Ctree * eta + Ctree * etaSrc ≤ sigma + (1 - sigma) / 2 :=
    add_le_add hbase (le_trans hsrc' hbudget)
  calc
    Ctree * (eta + etaSrc) = Ctree * eta + Ctree * etaSrc := by ring
    _ ≤ sigma + (1 - sigma) / 2 := hsum
    _ < 1 := by linarith

/-- The same source radius can be admitted simultaneously at a weak rooted
expansion and at a finite matching expansion, provided it fits inside both
strict margins. -/
theorem two_stage_source_margin_admission
    (Cw etaw sigmaw Lw Cm etam sigmam Lm rho srcw srcm : ℝ)
    (hCw : 0 ≤ Cw)
    (hCm : 0 ≤ Cm)
    (hbasew : Cw * etaw ≤ sigmaw)
    (hbasem : Cm * etam ≤ sigmam)
    (hsigmaw : sigmaw < 1)
    (hsigmam : sigmam < 1)
    (hsrcw : srcw ≤ Lw * rho)
    (hsrcm : srcm ≤ Lm * rho)
    (hsmallw : 2 * Cw * Lw * rho ≤ 1 - sigmaw)
    (hsmallm : 2 * Cm * Lm * rho ≤ 1 - sigmam) :
    Cw * (etaw + srcw) < 1 ∧ Cm * (etam + srcm) < 1 := by
  constructor
  · exact strict_root_margin_absorbs_source
      Cw etaw sigmaw Lw rho srcw hCw hbasew hsigmaw hsrcw hsmallw
  · exact strict_root_margin_absorbs_source
      Cm etam sigmam Lm rho srcm hCm hbasem hsigmam hsrcm hsmallm

#print axioms strict_root_margin_absorbs_source
#print axioms two_stage_source_margin_admission

end Millennium.YangMills
