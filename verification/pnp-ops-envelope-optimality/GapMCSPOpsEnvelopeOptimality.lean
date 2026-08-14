import Mathlib

/-!
# Gap-MCSP OPS linear-envelope optimality: standalone finite logical core

This public replay file formalizes only the real-inequality / quantifier core.
It does not define circuits, Gap-MCSP, NP, P/poly, or prove P != NP.
-/

namespace Millennium.PNP.GapMCSPOpsEnvelopeOptimality

/-- A local linear ratio bound blocks the exact strict hard-point selector needed
by an OPS-style easy envelope with the same budget `K`. -/
theorem boundedRatioBlocksLinearConflict
    (Hard : ℝ → ℝ → Prop)
    (K beta0 : ℝ)
    (hBound : ∀ beta eta : ℝ,
      0 < beta → 0 < eta → beta < beta0 → Hard beta eta → eta ≤ K * beta) :
    ¬ ∃ beta eta : ℝ,
      0 < beta ∧ 0 < eta ∧ beta < beta0 ∧ K * beta < eta ∧ Hard beta eta := by
  rintro ⟨beta, eta, hBeta, hEta, hSmall, hMargin, hHard⟩
  have hLe := hBound beta eta hBeta hEta hSmall hHard
  linarith

/-- Cofinal hard points rule out every positive local linear ratio bound. -/
theorem cofinalExcludesLocalLinearBound
    (Hard : ℝ → ℝ → Prop)
    (hCofinal : ∀ A delta : ℝ,
      0 < A → 0 < delta →
      ∃ beta eta : ℝ,
        0 < beta ∧ 0 < eta ∧ beta < delta ∧ A * beta < eta ∧ Hard beta eta) :
    ¬ ∃ K beta0 : ℝ,
      0 < K ∧ 0 < beta0 ∧
      ∀ beta eta : ℝ,
        0 < beta → 0 < eta → beta < beta0 → Hard beta eta → eta ≤ K * beta := by
  rintro ⟨K, beta0, hK, hBeta0, hBound⟩
  rcases hCofinal K beta0 hK hBeta0 with
    ⟨beta, eta, hBeta, hEta, hSmall, hMargin, hHard⟩
  have hLe := hBound beta eta hBeta hEta hSmall hHard
  linarith

/-- A bounded hard profile is parameter-wise compatible with the matching easy
linear envelope: the strict exponent conflict cannot fire. -/
theorem boundedProfileCompatibleWithLinearEnvelope
    (Easy Hard : ℝ → ℝ → Prop)
    (K beta0 : ℝ)
    (hBound : ∀ beta eta : ℝ,
      0 < beta → 0 < eta → beta < beta0 → Hard beta eta → eta ≤ K * beta)
    (hEasy : ∀ beta : ℝ,
      0 < beta → beta < beta0 → Easy beta (K * beta)) :
    ∀ beta eta : ℝ,
      0 < beta → 0 < eta → beta < beta0 → Hard beta eta →
      Easy beta (K * beta) ∧ ¬ (K * beta < eta) := by
  intro beta eta hBeta hEta hSmall hHard
  constructor
  · exact hEasy beta hBeta hSmall
  · have hLe := hBound beta eta hBeta hEta hSmall hHard
    linarith

#print axioms boundedRatioBlocksLinearConflict
#print axioms cofinalExcludesLocalLinearBound
#print axioms boundedProfileCompatibleWithLinearEnvelope

end Millennium.PNP.GapMCSPOpsEnvelopeOptimality
