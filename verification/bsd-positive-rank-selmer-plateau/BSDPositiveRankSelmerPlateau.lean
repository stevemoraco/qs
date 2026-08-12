import Mathlib

/-!
# Positive-rank corrected Selmer plateau: finite algebraic core

A list `depths` models the elementary-divisor depths of a hidden finite
p-primary group. `growth depths m` is the p-length visible at level `p^m`.
`selmerGrowth rank depths m` adds the free Mordell–Weil contribution `m*rank`.

This file formalizes only the finite arithmetic core. It does not define an
elliptic curve, a Selmer group, a Tate–Shafarevich group, a regulator, or BSD.
-/

namespace BSDPositiveRankSelmerPlateau

/-- Visible p-length of hidden cyclic factors at level `p^m`. -/
def growth : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: depths, m => Nat.min m a + growth depths m

/-- Number of hidden cyclic factors whose depth is still greater than `m`. -/
def deepCount : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: depths, m => (if m < a then 1 else 0) + deepCount depths m

/-- Abstract finite-level Selmer length after adding a free rank contribution. -/
def selmerGrowth (rank : ℕ) (depths : List ℕ) (m : ℕ) : ℕ :=
  m * rank + growth depths m

/-- Each step reveals exactly one additional unit from every factor deeper than
that step. -/
theorem growth_succ (depths : List ℕ) (m : ℕ) :
    growth depths (m + 1) = growth depths m + deepCount depths m := by
  induction depths with
  | nil => simp [growth, deepCount]
  | cons a depths ih =>
      simp only [growth, deepCount]
      rw [ih]
      by_cases h : m < a
      · rw [Nat.min_eq_left (Nat.le_of_lt h), Nat.min_eq_left h]
        simp [h]
        omega
      · have ham : a ≤ m := Nat.le_of_not_gt h
        have hasucc : a ≤ m + 1 := Nat.le_trans ham (Nat.le_add_right m 1)
        rw [Nat.min_eq_right ham, Nat.min_eq_right hasucc]
        simp [h, Nat.add_assoc]

/-- No factor remains deeper than `m` exactly when the deep-factor count is
zero. -/
theorem deepCount_eq_zero_iff (depths : List ℕ) (m : ℕ) :
    deepCount depths m = 0 ↔ ∀ a ∈ depths, a ≤ m := by
  induction depths with
  | nil => simp [deepCount]
  | cons a depths ih =>
      by_cases h : m < a
      · simp [deepCount, h]
      · have ham : a ≤ m := Nat.le_of_not_gt h
        simp [deepCount, h, ham, ih]

/-- A consecutive-level plateau is equivalent to complete saturation at the
current level. -/
theorem growth_plateau_iff (depths : List ℕ) (m : ℕ) :
    growth depths (m + 1) = growth depths m ↔
      ∀ a ∈ depths, a ≤ m := by
  constructor
  · intro h
    rw [growth_succ] at h
    have hc : deepCount depths m = 0 := by omega
    exact (deepCount_eq_zero_iff depths m).1 hc
  · intro hall
    have hc : deepCount depths m = 0 :=
      (deepCount_eq_zero_iff depths m).2 hall
    rw [growth_succ, hc]
    simp

/-- Once every depth is at most `m`, the visible length equals the total hidden
length. -/
theorem growth_eq_total_of_saturated
    (depths : List ℕ) (m : ℕ)
    (hall : ∀ a ∈ depths, a ≤ m) :
    growth depths m = depths.sum := by
  induction depths with
  | nil => simp [growth]
  | cons a depths ih =>
      have ha : a ≤ m := hall a (by simp)
      have htail : ∀ b ∈ depths, b ≤ m := by
        intro b hb
        exact hall b (by simp [hb])
      simp [growth, Nat.min_eq_right ha, ih htail]

/-- The positive-rank repair: a raw Selmer increment equal to the free rank is
exactly the corrected hidden-group plateau. -/
theorem rank_corrected_increment_iff_saturation
    (rank : ℕ) (depths : List ℕ) (m : ℕ) :
    selmerGrowth rank depths (m + 1) =
        selmerGrowth rank depths m + rank ↔
      ∀ a ∈ depths, a ≤ m := by
  have hs : (m + 1) * rank = m * rank + rank := by
    simp [Nat.add_mul]
  constructor
  · intro h
    have hplateau : growth depths (m + 1) = growth depths m := by
      unfold selmerGrowth at h
      rw [hs] at h
      omega
    exact (growth_plateau_iff depths m).1 hplateau
  · intro hall
    have hplateau := (growth_plateau_iff depths m).2 hall
    unfold selmerGrowth
    rw [hs, hplateau]
    omega

/-- Two corrected target equalities close both saturation and the exact total
hidden length. -/
theorem two_level_target_closure
    (rank target m : ℕ) (depths : List ℕ)
    (hm : selmerGrowth rank depths m = m * rank + target)
    (hnext :
      selmerGrowth rank depths (m + 1) = (m + 1) * rank + target) :
    depths.sum = target ∧ ∀ a ∈ depths, a ≤ m := by
  have hgm : growth depths m = target := by
    unfold selmerGrowth at hm
    exact Nat.add_left_cancel hm
  have hgnext : growth depths (m + 1) = target := by
    unfold selmerGrowth at hnext
    exact Nat.add_left_cancel hnext
  have hplateau : growth depths (m + 1) = growth depths m := by
    omega
  have hall := (growth_plateau_iff depths m).1 hplateau
  have htotal := growth_eq_total_of_saturated depths m hall
  constructor
  · omega
  · exact hall

/-- CRITIC: one corrected finite level can match a target while a deeper cyclic
factor remains unseen. -/
theorem one_level_can_hide_deeper (rank m : ℕ) :
    selmerGrowth rank [m + 1] m = m * rank + m ∧
      [m + 1].sum = m + 1 := by
  simp [selmerGrowth, growth]

/-- CRITIC: the same first two raw Selmer lengths can come from different rank
and hidden-torsion models. Thus rank cannot be inferred by silently choosing a
subtraction. -/
theorem rank_sha_two_level_nonidentifiability :
    selmerGrowth 2 [] 1 = selmerGrowth 1 [2] 1 ∧
    selmerGrowth 2 [] 2 = selmerGrowth 1 [2] 2 ∧
    ([] : List ℕ).sum ≠ [2].sum ∧
    (2 : ℕ) ≠ 1 := by
  norm_num [selmerGrowth, growth]

#print axioms growth_succ
#print axioms deepCount_eq_zero_iff
#print axioms growth_plateau_iff
#print axioms growth_eq_total_of_saturated
#print axioms rank_corrected_increment_iff_saturation
#print axioms two_level_target_closure
#print axioms one_level_can_hide_deeper
#print axioms rank_sha_two_level_nonidentifiability

end BSDPositiveRankSelmerPlateau
