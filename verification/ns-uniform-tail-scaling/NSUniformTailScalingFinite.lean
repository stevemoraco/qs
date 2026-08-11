import Mathlib

/-!
# Navier--Stokes uniform-tail obstruction: finite scaling and quantifier core

Honesty status: this file formalizes only rational scaling identities and an
abstract pointwise-versus-uniform quantifier countermodel. It does not formalize
smooth divergence-free packets, Lorentz spaces, the Navier--Stokes equations,
Leray--Hopf solutions, or the Clay statement.
-/

namespace MillenniumBraid
namespace NSUniformTailScalingFinite

theorem velocityWeakL3Exponent :
    (-1 : ℚ) + 3 * (1 / 3 : ℚ) = 0 := by
  norm_num

theorem vorticityWeakLThreeHalvesExponent :
    (-2 : ℚ) + 3 * (2 / 3 : ℚ) = 0 := by
  norm_num

theorem kineticEnergyExponent :
    2 * (-1 : ℚ) + 3 = 1 := by
  norm_num

theorem instantaneousEnstrophyExponent :
    2 * (-2 : ℚ) + 3 = -1 := by
  norm_num

theorem parabolicDissipationExponent :
    2 + 2 * (-2 : ℚ) + 3 = 1 := by
  norm_num

theorem timeDerivativeLedgerExponent :
    2 + (4 / 3 : ℚ) * (-1 / 2 : ℚ) = 4 / 3 := by
  norm_num

theorem lerayLinePacketExponent
    (q : ℝ) (hq0 : q ≠ 0) (hq2 : q ≠ 2) :
    2 + (4 * q / (3 * (q - 2))) * (3 / q - 1)
      = (4 * q / (3 * (q - 2))) / 2 := by
  field_simp
  ring

theorem lerayLinePacketExponentPositive
    (q : ℝ) (hq : 2 < q) :
    0 < (2 * q) / (3 * (q - 2)) := by
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  have hden : 0 < 3 * (q - 2) := mul_pos (by norm_num) (sub_pos.mpr hq)
  exact div_pos (mul_pos (by norm_num) hq0) hden

def diagonalTail (n K : ℕ) : ℝ :=
  if K ≤ n then 1 else 0

theorem diagonalTailPointwiseVanishes (n K : ℕ) (hK : n < K) :
    diagonalTail n K = 0 := by
  simp [diagonalTail, Nat.not_le.mpr hK]

theorem diagonalTailUniformFailure (K : ℕ) :
    diagonalTail K K = 1 := by
  simp [diagonalTail]

theorem pointwiseButNotUniform :
    (∀ n : ℕ, ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → diagonalTail n K = 0) ∧
    (∀ K₀ : ℕ, ∃ n K : ℕ, K₀ ≤ K ∧ diagonalTail n K = 1) := by
  constructor
  · intro n
    refine ⟨n + 1, ?_⟩
    intro K hK
    apply diagonalTailPointwiseVanishes
    omega
  · intro K₀
    exact ⟨K₀, K₀, le_rfl, diagonalTailUniformFailure K₀⟩

#print axioms velocityWeakL3Exponent
#print axioms vorticityWeakLThreeHalvesExponent
#print axioms kineticEnergyExponent
#print axioms instantaneousEnstrophyExponent
#print axioms parabolicDissipationExponent
#print axioms timeDerivativeLedgerExponent
#print axioms lerayLinePacketExponent
#print axioms lerayLinePacketExponentPositive
#print axioms diagonalTailPointwiseVanishes
#print axioms diagonalTailUniformFailure
#print axioms pointwiseButNotUniform

end NSUniformTailScalingFinite
end MillenniumBraid
