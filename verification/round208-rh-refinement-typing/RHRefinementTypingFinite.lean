import Mathlib

/-!
# Round 208 RH refinement typing finite cores

This file formalizes only scalar composition and frame-energy bookkeeping. It
does not formalize B-splines, prime statistics, Fourier transforms, zeta, or RH.
-/

namespace Millennium
namespace Round208RH

/-- One refinement step multiplies a scalar mode by its step multiplier. -/
def refineStep (multiplier input : ℝ) : ℝ := multiplier * input

/-- The actual two-step nested output applies the second multiplier to the
first output, and hence carries the product of both multipliers. -/
theorem nested_refinement_is_composition
    (first second input : ℝ) :
    refineStep second (refineStep first input) =
      (second * first) * input := by
  simp [refineStep]
  ring

/-- Applying the second operator directly to the original input is a different
channel from applying it to the first output. -/
theorem companion_minus_nested_identity
    (first second input : ℝ) :
    refineStep second input -
        refineStep second (refineStep first input) =
      second * (1 - first) * input := by
  simp [refineStep]
  ring

/-- A blind first refinement remains blind after every subsequent scalar
refinement step. -/
theorem blind_mode_propagates_to_nested_output
    (second input : ℝ) :
    refineStep second (refineStep 0 input) = 0 := by
  simp [refineStep]

/-- The actual nested two-channel energy has the common first-factor square. -/
theorem nested_two_channel_energy_factorization
    (first second : ℝ) :
    first ^ 2 + (second * first) ^ 2 =
      first ^ 2 * (1 + second ^ 2) := by
  ring

/-- Consequently the nested two-channel energy vanishes at every blind first
multiplier, regardless of the second multiplier. -/
theorem nested_two_channel_blind
    (second : ℝ) :
    0 ^ 2 + (second * 0) ^ 2 = 0 := by
  ring

/-- By contrast, the direct companion-channel energy need not vanish when the
first multiplier is blind. -/
theorem companion_channel_removes_one_blind_mode :
    0 ^ 2 + (1 : ℝ) ^ 2 = 1 := by
  norm_num

/-- A lower frame bound for direct multipliers `first, second` cannot be reused
for the nested pair `first, second*first`: the explicit scalar counterexample
has direct energy one and nested energy zero. -/
theorem direct_frame_does_not_imply_nested_frame :
    (1 : ℝ) ≤ 0 ^ 2 + 1 ^ 2 ∧
      ¬ (1 : ℝ) ≤ 0 ^ 2 + (1 * 0) ^ 2 := by
  norm_num

/-- If a weighted first-channel energy can approach zero while the second
factor stays bounded by `B`, the nested pair can approach zero as well. -/
theorem nested_weighted_degeneracy_budget
    (firstSq secondSq B eps : ℝ)
    (hfirst : 0 ≤ firstSq)
    (hsecond : 0 ≤ secondSq)
    (hbound : secondSq ≤ B)
    (hB : 0 ≤ B)
    (heps : firstSq ≤ eps / (1 + B))
    (heps0 : 0 ≤ eps) :
    firstSq * (1 + secondSq) ≤ eps := by
  have hden : 0 < 1 + B := by linarith
  have hone : 0 ≤ 1 + secondSq := by linarith
  calc
    firstSq * (1 + secondSq) ≤
        (eps / (1 + B)) * (1 + secondSq) :=
      mul_le_mul_of_nonneg_right heps hone
    _ ≤ (eps / (1 + B)) * (1 + B) := by
      have hquot : 0 ≤ eps / (1 + B) := div_nonneg heps0 (le_of_lt hden)
      exact mul_le_mul_of_nonneg_left (by linarith) hquot
    _ = eps := by field_simp

#print axioms nested_refinement_is_composition
#print axioms companion_minus_nested_identity
#print axioms blind_mode_propagates_to_nested_output
#print axioms nested_two_channel_energy_factorization
#print axioms nested_two_channel_blind
#print axioms companion_channel_removes_one_blind_mode
#print axioms direct_frame_does_not_imply_nested_frame
#print axioms nested_weighted_degeneracy_budget

end Round208RH
end Millennium
