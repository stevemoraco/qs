import Mathlib

/-!
# C410 finite stable-contraction transfer

This file formalizes only the finite norm inequalities behind C410.

A strict contraction plus a controlled additive derivative defect has
contraction constant `q + eta`. A spare margin survives whenever the defect is
smaller than that margin. The file does not formalize derivatives, Banach
charts, RG maps, Balaban's theorem, norm dictionaries, or Yang--Mills.
-/

namespace Millennium.YangMills.FaizalShabirStableContractionTransfer

variable {V : Type*} [NormedAddCommGroup V]

/-- A pointwise contraction estimate plus a pointwise additive map defect gives
contraction with the sum of the two constants. -/
theorem contractionPlusAdditiveDefect
    (balaban fs : V → V)
    (x : V) (q eta : ℝ)
    (hBalaban : ‖balaban x‖ ≤ q * ‖x‖)
    (hDefect : ‖fs x - balaban x‖ ≤ eta * ‖x‖) :
    ‖fs x‖ ≤ (q + eta) * ‖x‖ := by
  rw [show fs x = (fs x - balaban x) + balaban x by abel]
  calc
    ‖(fs x - balaban x) + balaban x‖
        ≤ ‖fs x - balaban x‖ + ‖balaban x‖ := norm_add_le _ _
    _ ≤ eta * ‖x‖ + q * ‖x‖ := add_le_add hDefect hBalaban
    _ = (q + eta) * ‖x‖ := by ring

/-- If a reference contraction has spare margin `kappa` and the transferred
defect is strictly smaller than that margin, the transferred constant is still
strictly below one. The positivity of `kappa` follows from the two displayed
inequalities and is therefore not needed as a separate premise. -/
theorem strictMarginSurvives
    (q eta kappa : ℝ)
    (hq : q ≤ 1 - kappa)
    (heta : eta < kappa) :
    q + eta < 1 := by
  linarith

/-- A half-margin defect leaves at least half of the original strict margin.
No separate nonnegativity premise is required for the algebraic implication. -/
theorem halfMarginSurvives
    (q eta kappa : ℝ)
    (hq : q ≤ 1 - kappa)
    (heta : eta ≤ kappa / 2) :
    q + eta ≤ 1 - kappa / 2 := by
  linarith

#print axioms contractionPlusAdditiveDefect
#print axioms strictMarginSurvives
#print axioms halfMarginSurvives

end Millennium.YangMills.FaizalShabirStableContractionTransfer
