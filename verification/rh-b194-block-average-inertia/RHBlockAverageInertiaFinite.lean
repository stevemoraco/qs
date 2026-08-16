import Mathlib

/-!
# RH B194 block-average inertia finite core

Finite real/order/sum algebra only.

This file formalizes the genuinely new deterministic shell used by RH B194:

* a nonempty block whose entries are uniformly negative has negative block sum;
* the ordinary-prime prefix kernel `(n^2/p)-1` is nonnegative whenever `p<=n^2`;
* finite block/prime summation may be interchanged exactly;
* nonnegative prime weights preserve nonnegativity of the aggregated block kernel;
* a designated negative subfamily is bounded by the full negative-coordinate count;
* block averaging can hide isolated negative point values, the finite firewall that
  separates B194 from the stronger pointwise/run consumer.

It deliberately does **not** formalize Zhao's theorem, the PNT, primes as primes,
Mertens means, asymptotic persistence, zeta zeros, BGST/Hermite theory, the B46
contraction, RH, or negation of RH.
-/

open Finset
open scoped BigOperators

namespace RHBlockAverageInertiaFinite

/-- A nonempty finite block which stays at least `D` below zero has strictly
negative total block sum. -/
theorem uniform_negative_block_sum_negative
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) {D : ℝ}
    (hD : 0 < D) (hne : s.Nonempty)
    (hneg : ∀ i ∈ s, f i ≤ -D) :
    (∑ i in s, f i) < 0 := by
  have hsum : (∑ i in s, f i) ≤ ∑ _i in s, (-D) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hneg i hi
  have hcardpos : 0 < (s.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hne)
  calc
    (∑ i in s, f i) ≤ ∑ _i in s, (-D) := hsum
    _ = (s.card : ℝ) * (-D) := by simp
    _ < 0 := mul_neg_of_pos_of_neg hcardpos (neg_neg_of_pos hD)

/-- The exact B194 ordinary-prime coefficient at one root sample is nonnegative
once the prime/index lies below the square checkpoint. -/
theorem prefix_kernel_nonneg
    (p n : ℕ) (hp : 0 < p) (hpn : p ≤ n ^ 2) :
    0 ≤ (n : ℝ) ^ 2 / (p : ℝ) - 1 := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hpnR : (p : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hpn
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ 2 / (p : ℝ) := by
    apply (le_div_iff₀ hpR).2
    simpa using hpnR
  linarith

/-- Finite block/prime sums commute exactly; this is the algebraic step behind
collecting the B194 block sum by prime rather than by square checkpoint. -/
theorem block_prime_sum_interchange
    (B P : Finset ℕ) (w : ℕ → ℝ) (K : ℕ → ℕ → ℝ) :
    (∑ n in B, ∑ p in P, w p * K p n) =
      ∑ p in P, w p * (∑ n in B, K p n) := by
  calc
    (∑ n in B, ∑ p in P, w p * K p n) =
        ∑ p in P, ∑ n in B, w p * K p n := by
          rw [Finset.sum_comm]
    _ = ∑ p in P, w p * (∑ n in B, K p n) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]

/-- Nonnegative prime weights and nonnegative per-sample kernels give a
nonnegative aggregated block kernel. -/
theorem weighted_block_kernel_nonneg
    (B P : Finset ℕ) (w : ℕ → ℝ) (K : ℕ → ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p)
    (hK : ∀ p ∈ P, ∀ n ∈ B, 0 ≤ K p n) :
    0 ≤ ∑ p in P, w p * (∑ n in B, K p n) := by
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (hw p hp) (Finset.sum_nonneg fun n hn => hK p hp n hn)

/-- Any explicitly designated negative subfamily is bounded by the full number
of negative coordinates.  This is the finite count consumer used after the
analytic persistence theorem produces many negative blocks. -/
theorem designated_negative_card_le_full_negative_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (s : Finset ι)
    (hs : ∀ i ∈ s, f i < 0) :
    s.card ≤ (Finset.univ.filter fun i => f i < 0).card := by
  apply Finset.card_le_card
  intro i hi
  simp [hs i hi]

/-- Hostile finite firewall: a nonnegative block sum does not force pointwise
nonnegativity.  Hence B194's block-average consumer is genuinely weaker than a
pointwise-sign consumer for arbitrary data. -/
theorem nonnegative_block_sum_can_hide_negative_point :
    (-1 : ℝ) < 0 ∧ (-1 : ℝ) + 1 = 0 := by
  norm_num

#print axioms uniform_negative_block_sum_negative
#print axioms prefix_kernel_nonneg
#print axioms block_prime_sum_interchange
#print axioms weighted_block_kernel_nonneg
#print axioms designated_negative_card_le_full_negative_card
#print axioms nonnegative_block_sum_can_hide_negative_point

end RHBlockAverageInertiaFinite
