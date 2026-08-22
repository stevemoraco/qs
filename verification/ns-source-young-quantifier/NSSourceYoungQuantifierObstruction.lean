import Mathlib

namespace NS
namespace SourceYoungQuantifierObstruction

theorem fixed_remainder_cannot_absorb_larger_linear_slope
    (k delta C : ℝ)
    (hC : 0 ≤ C)
    (hgap : 3 * delta < k) :
    ∃ T : ℝ, 0 ≤ T ∧ k * T > delta * (T + T + T) + C := by
  let gap : ℝ := k - 3 * delta
  have hgapPos : 0 < gap := by
    dsimp [gap]
    linarith
  let T : ℝ := (C + 1) / gap
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  have hgapT : gap * T = C + 1 := by
    dsimp [T]
    field_simp
  refine ⟨T, hT, ?_⟩
  dsimp [gap] at hgapT
  ring_nf at hgapT ⊢
  linarith

theorem no_uniform_additive_remainder_below_slope
    (k delta : ℝ)
    (hgap : 3 * delta < k) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      k * T ≤ delta * (T + T + T) + C := by
  rintro ⟨C, hC, hAll⟩
  obtain ⟨T, hT, hFail⟩ :=
    fixed_remainder_cannot_absorb_larger_linear_slope k delta C hC hgap
  exact (not_lt_of_ge (hAll T hT)) hFail

theorem synchronized_slope_absorbs_diagonal
    (k delta T : ℝ)
    (hT : 0 ≤ T)
    (hsync : k ≤ 3 * delta) :
    k * T ≤ delta * (T + T + T) := by
  nlinarith

theorem quadratic_threshold_synchronizes_slope
    (epsilon k delta : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hk : 0 ≤ k)
    (hdelta : 0 ≤ delta)
    (hkSq : k ^ 2 ≤ epsilon)
    (hthreshold : epsilon ≤ 9 * delta ^ 2) :
    k ≤ 3 * delta := by
  nlinarith [sq_nonneg (k - 3 * delta)]

theorem quadratic_threshold_absorbs_diagonal
    (epsilon k delta T : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hk : 0 ≤ k)
    (hdelta : 0 ≤ delta)
    (hT : 0 ≤ T)
    (hkSq : k ^ 2 ≤ epsilon)
    (hthreshold : epsilon ≤ 9 * delta ^ 2) :
    k * T ≤ delta * (T + T + T) := by
  exact synchronized_slope_absorbs_diagonal k delta T hT
    (quadratic_threshold_synchronizes_slope
      epsilon k delta hepsilon hk hdelta hkSq hthreshold)

#print axioms fixed_remainder_cannot_absorb_larger_linear_slope
#print axioms no_uniform_additive_remainder_below_slope
#print axioms synchronized_slope_absorbs_diagonal
#print axioms quadratic_threshold_synchronizes_slope
#print axioms quadratic_threshold_absorbs_diagonal

end SourceYoungQuantifierObstruction
end NS
