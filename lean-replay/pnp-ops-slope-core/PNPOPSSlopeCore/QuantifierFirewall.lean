import Mathlib

/-!
# Quantifier firewall for unbounded-slope hardness magnification

This file formalizes only the logical/arithmetic core of an OPS proof-parameter
refinement. `Hard β η` is an abstract lower-bound predicate and `Contain` is an
abstract containment proposition. The file does not formalize Boolean circuits,
Gap-MCSP, NP, P/poly, or P versus NP.

There are no user-declared axioms or proof placeholders.
-/

namespace PNPOPSSlopeCore

/-- An upper envelope with one unknown fixed slope is incompatible with lower
bounds beating every fixed slope at arbitrarily small positive parameters. -/
theorem unbounded_slope_contradicts_upper_envelope
    (Hard : ℚ → ℚ → Prop) (Contain : Prop)
    (hupper : Contain →
      ∃ K β₀ : ℚ, 0 < K ∧ 0 < β₀ ∧
        ∀ β η : ℚ, 0 < β → β < β₀ → K * β < η → ¬ Hard β η)
    (hlower : ∀ K β₀ : ℚ, 0 < K → 0 < β₀ →
      ∃ β η : ℚ, 0 < β ∧ β < β₀ ∧ K * β < η ∧ Hard β η) :
    ¬ Contain := by
  intro hContain
  obtain ⟨K, β₀, hK, hβ₀, henv⟩ := hupper hContain
  obtain ⟨β, η, hβ, hsmall, hslope, hHard⟩ :=
    hlower K β₀ hK hβ₀
  exact (henv β η hβ hsmall hslope) hHard

/-- Sequence form: no analytic limit operation is needed. The exact required
condition is that the sequence reaches arbitrarily small positive `β` while
its excess exponent beats every fixed slope. -/
theorem sequence_unbounded_slope_contradicts_upper_envelope
    (Hard : ℚ → ℚ → Prop) (Contain : Prop)
    (β η : ℕ → ℚ)
    (hupper : Contain →
      ∃ K β₀ : ℚ, 0 < K ∧ 0 < β₀ ∧
        ∀ b e : ℚ, 0 < b → b < β₀ → K * b < e → ¬ Hard b e)
    (hHard : ∀ j : ℕ, Hard (β j) (η j))
    (hunbounded : ∀ K β₀ : ℚ, 0 < K → 0 < β₀ →
      ∃ j : ℕ, 0 < β j ∧ β j < β₀ ∧ K * β j < η j) :
    ¬ Contain := by
  apply unbounded_slope_contradicts_upper_envelope Hard Contain hupper
  intro K β₀ hK hβ₀
  obtain ⟨j, hβ, hsmall, hslope⟩ := hunbounded K β₀ hK hβ₀
  exact ⟨β j, η j, hβ, hsmall, hslope, hHard j⟩

/-- A single fixed positive slope `η=Cβ` cannot beat an unknown upper-envelope
slope. This is the exact quantifier obstruction to replacing unbounded slope
by one universal constant multiple of `β`. -/
theorem fixed_slope_not_unbounded
    (C : ℚ) (hC : 0 ≤ C) :
    ¬ (∀ K β₀ : ℚ, 0 < K → 0 < β₀ →
      ∃ β : ℚ, 0 < β ∧ β < β₀ ∧ K * β < C * β) := by
  intro h
  obtain ⟨β, hβ, _hsmall, hslope⟩ :=
    h (C + 1) 1 (by linarith) (by norm_num)
  nlinarith

end PNPOPSSlopeCore
