import Mathlib

/-!
# RH B199 catastrophic block-count finite core

Finite real/order/cardinality algebra only.

This file formalizes the genuinely new deterministic shell used by RH B199:

* a catastrophic negative threshold is exactly a zero-threshold test after a
  positive scalar shift;
* a uniformly depth-`D` negative block crosses a block threshold built from any
  smaller depth `T`;
* catastrophic negativity is a subfamily of ordinary negativity when the
  threshold is nonnegative;
* the shifted negative-coordinate count equals the catastrophic-coordinate count;
* mild negative data may be invisible to a deeper catastrophic threshold, the
  finite firewall separating B199 from B194.

It deliberately does **not** formalize Zhao's theorem, the PNT, primes as primes,
Mertens means, asymptotic persistence, zeta zeros, BGST/Hermite theory, the B46
contraction, RH, or negation of RH.
-/

open Finset
open scoped BigOperators

namespace RHCatastrophicBlockCountFinite

/-- Catastrophic negativity at depth `T` is exactly ordinary negativity after
shifting upward by `T`. -/
theorem deep_negative_iff_shift_negative (x T : ℝ) :
    x < -T ↔ x + T < 0 := by
  linarith

/-- If every entry of a nonempty finite block lies at least `D` below zero and
`D` is strictly larger than the target depth `T`, then the block sum lies below
`-card * T`.  This is the finite threshold step used after B191 supplies uniform
depth throughout a whole root interval. -/
theorem uniform_depth_crosses_block_threshold
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) (D T : ℝ)
    (hne : s.Nonempty) (hTD : T < D)
    (hneg : ∀ i ∈ s, f i ≤ -D) :
    (∑ i in s, f i) < -(s.card : ℝ) * T := by
  have hsum : (∑ i in s, f i) ≤ ∑ _i in s, (-D) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hneg i hi
  have hcardpos : 0 < (s.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hne)
  calc
    (∑ i in s, f i) ≤ ∑ _i in s, (-D) := hsum
    _ = (s.card : ℝ) * (-D) := by simp
    _ < (s.card : ℝ) * (-T) :=
      mul_lt_mul_of_pos_left (neg_lt_neg hTD) hcardpos
    _ = -(s.card : ℝ) * T := by ring

/-- With a nonnegative catastrophic depth, every catastrophic coordinate is in
particular negative. -/
theorem deep_negative_is_negative
    {x T : ℝ} (hT : 0 ≤ T) (hx : x < -T) :
    x < 0 := by
  linarith

/-- The shifted negative-coordinate set and the catastrophic-coordinate set are
identical.  This is the finite diagonal-inertia normalization used by B199. -/
theorem shifted_negative_count_eq_deep_count
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (T : ℝ) :
    (Finset.univ.filter fun i => f i + T < 0).card =
      (Finset.univ.filter fun i => f i < -T).card := by
  apply congrArg Finset.card
  ext i
  simp [deep_negative_iff_shift_negative]

/-- Any explicitly designated catastrophic subfamily is bounded by the shifted
negative-coordinate count. -/
theorem designated_deep_card_le_shift_negative_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (T : ℝ) (s : Finset ι)
    (hs : ∀ i ∈ s, f i < -T) :
    s.card ≤ (Finset.univ.filter fun i => f i + T < 0).card := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (deep_negative_iff_shift_negative (f i) T).1 (hs i hi)

/-- Hostile finite firewall: mild negative block sums can all escape a deeper
catastrophic threshold.  Hence B199 is strictly weaker than B194 as a finite
consumer. -/
theorem mild_negative_can_escape_deep_threshold :
    (-1 : ℝ) < 0 ∧ ¬ ((-1 : ℝ) < -2) := by
  norm_num

#print axioms deep_negative_iff_shift_negative
#print axioms uniform_depth_crosses_block_threshold
#print axioms deep_negative_is_negative
#print axioms shifted_negative_count_eq_deep_count
#print axioms designated_deep_card_le_shift_negative_card
#print axioms mild_negative_can_escape_deep_threshold

end RHCatastrophicBlockCountFinite
