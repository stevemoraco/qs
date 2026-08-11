import Mathlib

/-!
# P versus NP robust randomized averaging core

Finite logical core only. This file does not prove `P ≠ NP` or `P = NP`.

It formalizes the quantifier-safe passage used by the robust bounded-congestion lane:
if every deterministic circuit has at least a `δ` average loss on one common finite
witness universe, then every probability mixture of those circuits has some witness
whose mixture loss is at least `δ`.
-/

namespace MillenniumB4
namespace PvsNPRobustRandomizedAveraging

/-- A convex combination preserves a common scalar lower bound. -/
theorem mixture_preserves_lower_bound
    {C : Type*} [Fintype C]
    (p loss : C → ℝ) (δ : ℝ)
    (hp_nonneg : ∀ c : C, 0 ≤ p c)
    (hp_sum : (∑ c : C, p c) = 1)
    (hloss : ∀ c : C, δ ≤ loss c) :
    δ ≤ ∑ c : C, p c * loss c := by
  calc
    δ = ∑ c : C, p c * δ := by
      rw [← Finset.sum_mul, hp_sum, one_mul]
    _ ≤ ∑ c : C, p c * loss c := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hloss c) (hp_nonneg c)

/--
If every deterministic circuit has total loss at least `L`, then any probability mixture
has total loss at least `L` on the same common witness universe.
-/
theorem randomized_total_loss_ge
    {C W : Type*} [Fintype C] [Fintype W]
    (p : C → ℝ) (err : C → W → ℝ) (L : ℝ)
    (hp_nonneg : ∀ c : C, 0 ≤ p c)
    (hp_sum : (∑ c : C, p c) = 1)
    (hdet : ∀ c : C, L ≤ ∑ w : W, err c w) :
    L ≤ ∑ w : W, ∑ c : C, p c * err c w := by
  have hmix : L ≤ ∑ c : C, p c * (∑ w : W, err c w) :=
    mixture_preserves_lower_bound p (fun c => ∑ w : W, err c w) L hp_nonneg hp_sum hdet
  calc
    L ≤ ∑ c : C, p c * (∑ w : W, err c w) := hmix
    _ = ∑ c : C, ∑ w : W, p c * err c w := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
    _ = ∑ w : W, ∑ c : C, p c * err c w := Finset.sum_comm

/--
Finite averaging principle in the normalization needed by the randomized-circuit bridge:
if the total is at least `|W| * δ`, one witness has value at least `δ`.
-/
theorem exists_ge_of_card_mul_le_sum
    {W : Type*} [Fintype W] [Nonempty W]
    (f : W → ℝ) (δ : ℝ)
    (hsum : (Fintype.card W : ℝ) * δ ≤ ∑ w : W, f w) :
    ∃ w : W, δ ≤ f w := by
  classical
  by_contra h
  push_neg at h
  have hlt : (∑ w : W, f w) < ∑ _w : W, δ := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro w hw
    exact h w
  have hconst : (∑ _w : W, δ) = (Fintype.card W : ℝ) * δ := by
    simp [nsmul_eq_mul]
  rw [hconst] at hlt
  exact (not_lt_of_ge hsum) hlt

/--
Main finite randomized bridge. If every deterministic member has total loss at least
`|W| * δ` on the same nonempty finite witness universe, then every nonnegative weight
vector of total mass one has some witness on which its mixture loss is at least `δ`.
-/
theorem randomized_witness_loss_ge
    {C W : Type*} [Fintype C] [Fintype W] [Nonempty W]
    (p : C → ℝ) (err : C → W → ℝ) (δ : ℝ)
    (hp_nonneg : ∀ c : C, 0 ≤ p c)
    (hp_sum : (∑ c : C, p c) = 1)
    (hdet : ∀ c : C,
      (Fintype.card W : ℝ) * δ ≤ ∑ w : W, err c w) :
    ∃ w : W, δ ≤ ∑ c : C, p c * err c w := by
  have htotal :
      (Fintype.card W : ℝ) * δ ≤
        ∑ w : W, ∑ c : C, p c * err c w :=
    randomized_total_loss_ge p err ((Fintype.card W : ℝ) * δ)
      hp_nonneg hp_sum hdet
  exact exists_ge_of_card_mul_le_sum
    (fun w => ∑ c : C, p c * err c w) δ htotal

end PvsNPRobustRandomizedAveraging
end MillenniumB4

#print axioms MillenniumB4.PvsNPRobustRandomizedAveraging.mixture_preserves_lower_bound
#print axioms MillenniumB4.PvsNPRobustRandomizedAveraging.randomized_total_loss_ge
#print axioms MillenniumB4.PvsNPRobustRandomizedAveraging.exists_ge_of_card_mul_le_sum
#print axioms MillenniumB4.PvsNPRobustRandomizedAveraging.randomized_witness_loss_ge
