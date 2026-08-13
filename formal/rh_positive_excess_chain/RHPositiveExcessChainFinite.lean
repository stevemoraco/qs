import Mathlib

/-!
Finite algebra for the positive Chebyshev-excess prime-cell chain rule.

This file does not define primes, the Chebyshev function, integrals,
convergence, Johnston's theorem, the zeta function, or RH.
-/

namespace RHPositiveExcessChain

/-- Positive part. -/
def posPart (x : ℝ) : ℝ := max x 0

/-- Quadratic positive-part energy. -/
noncomputable def energy (x : ℝ) : ℝ := (posPart x) ^ 2 / 2

/-- Difference between the endpoint rectangle and the positive-part energy
created by one nonnegative jump. -/
noncomputable def jumpRemainder (a ell : ℝ) : ℝ :=
  posPart (a + ell) * ell - (energy (a + ell) - energy a)

theorem posPart_nonnegative (x : ℝ) : 0 ≤ posPart x := by
  exact le_max_right x 0

theorem energy_nonnegative (x : ℝ) : 0 ≤ energy x := by
  unfold energy
  positivity

/-- The jump rectangle always dominates the positive-part energy increment. -/
theorem jumpRemainder_nonnegative
    (a ell : ℝ) (hell : 0 ≤ ell) :
    0 ≤ jumpRemainder a ell := by
  by_cases ha : 0 ≤ a
  · have hae : 0 ≤ a + ell := by linarith
    simp only [jumpRemainder, energy, posPart, max_eq_left ha,
      max_eq_left hae]
    nlinarith
  · have ha0 : a ≤ 0 := le_of_not_ge ha
    by_cases hae0 : a + ell ≤ 0
    · simp [jumpRemainder, energy, posPart, max_eq_right ha0,
        max_eq_right hae0]
    · have hae : 0 ≤ a + ell := le_of_lt (lt_of_not_ge hae0)
      simp only [jumpRemainder, energy, posPart, max_eq_right ha0,
        max_eq_left hae]
      have htwo : 0 ≤ 2 * ell - (a + ell) := by linarith
      have hprod : 0 ≤ (a + ell) * (2 * ell - (a + ell)) :=
        mul_nonneg hae htwo
      nlinarith

/-- The sharp universal overshoot bound for one jump. -/
theorem jumpRemainder_le_half_sq
    (a ell : ℝ) (hell : 0 ≤ ell) :
    jumpRemainder a ell ≤ ell ^ 2 / 2 := by
  by_cases ha : 0 ≤ a
  · have hae : 0 ≤ a + ell := by linarith
    simp only [jumpRemainder, energy, posPart, max_eq_left ha,
      max_eq_left hae]
    nlinarith
  · have ha0 : a ≤ 0 := le_of_not_ge ha
    by_cases hae0 : a + ell ≤ 0
    · simp only [jumpRemainder, energy, posPart, max_eq_right ha0,
        max_eq_right hae0]
      nlinarith [sq_nonneg ell]
    · have hae : 0 ≤ a + ell := le_of_lt (lt_of_not_ge hae0)
      simp only [jumpRemainder, energy, posPart, max_eq_right ha0,
        max_eq_left hae]
      nlinarith [sq_nonneg (ell - (a + ell))]

/-- Abstract one-cell chain rule. The analytic cell input is isolated in
`area = energy ePrev - energy a`. -/
theorem one_step_chain
    (ePrev a ell area : ℝ)
    (hArea : area = energy ePrev - energy a) :
    posPart (a + ell) * ell =
      energy (a + ell) - energy ePrev + area + jumpRemainder a ell := by
  unfold jumpRemainder
  rw [hArea]
  ring

/-- Finite weighted summation by parts for successive energy increments. -/
theorem weighted_telescope
    (n : ℕ) (w phi : ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 1),
        w k * (phi (k + 1) - phi k)) =
      w n * phi (n + 1) - w 0 * phi 0 +
        ∑ k ∈ Finset.range n,
          (w k - w (k + 1)) * phi (k + 1) := by
  induction n with
  | zero =>
      simp
      ring
  | succ n ih =>
      have hSourceSplit :
          (∑ k ∈ Finset.range (Nat.succ n + 1),
              w k * (phi (k + 1) - phi k)) =
            (∑ k ∈ Finset.range (n + 1),
              w k * (phi (k + 1) - phi k)) +
              w (n + 1) * (phi (n + 2) - phi (n + 1)) := by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
          (Finset.sum_range_succ
            (fun k => w k * (phi (k + 1) - phi k)) (n + 1))
      have hVariationSplit :
          (∑ k ∈ Finset.range (Nat.succ n),
              (w k - w (k + 1)) * phi (k + 1)) =
            (∑ k ∈ Finset.range n,
              (w k - w (k + 1)) * phi (k + 1)) +
              (w n - w (n + 1)) * phi (n + 1) := by
        simpa only [Nat.succ_eq_add_one] using
          (Finset.sum_range_succ
            (fun k => (w k - w (k + 1)) * phi (k + 1)) n)
      rw [hSourceSplit, ih, hVariationSplit]
      ring

/-- Exact finite four-ledger decomposition: terminal energy, weight variation,
cell area, and jump remainder. -/
theorem weighted_chain
    (n : ℕ)
    (w source phi area remainder : ℕ → ℝ)
    (hStep : ∀ k < n + 1,
      source k =
        phi (k + 1) - phi k + area k + remainder k) :
    (∑ k ∈ Finset.range (n + 1), w k * source k) =
      w n * phi (n + 1) - w 0 * phi 0 +
        ∑ k ∈ Finset.range n,
          (w k - w (k + 1)) * phi (k + 1) +
        ∑ k ∈ Finset.range (n + 1), w k * area k +
        ∑ k ∈ Finset.range (n + 1), w k * remainder k := by
  calc
    (∑ k ∈ Finset.range (n + 1), w k * source k) =
        ∑ k ∈ Finset.range (n + 1),
          w k * (phi (k + 1) - phi k + area k + remainder k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hStep k (Finset.mem_range.mp hk)]
    _ = (∑ k ∈ Finset.range (n + 1),
          w k * (phi (k + 1) - phi k)) +
        (∑ k ∈ Finset.range (n + 1), w k * area k) +
        (∑ k ∈ Finset.range (n + 1), w k * remainder k) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
    _ = _ := by
      rw [weighted_telescope]

/-- For nonnegative decreasing weights and a nonpositive initial energy, the
weighted cell-area budget is dominated by the weighted source ledger. -/
theorem area_budget_le_source
    (n : ℕ)
    (w source phi area remainder : ℕ → ℝ)
    (hStep : ∀ k < n + 1,
      source k =
        phi (k + 1) - phi k + area k + remainder k)
    (hW : ∀ k < n + 1, 0 ≤ w k)
    (hMono : ∀ k < n, w (k + 1) ≤ w k)
    (hPhi : ∀ k < n + 2, 0 ≤ phi k)
    (hPhi0 : phi 0 = 0)
    (hRem : ∀ k < n + 1, 0 ≤ remainder k) :
    (∑ k ∈ Finset.range (n + 1), w k * area k) ≤
      ∑ k ∈ Finset.range (n + 1), w k * source k := by
  rw [weighted_chain n w source phi area remainder hStep, hPhi0]
  simp only [mul_zero, sub_zero]
  have hBoundary : 0 ≤ w n * phi (n + 1) := by
    exact mul_nonneg (hW n (by omega)) (hPhi (n + 1) (by omega))
  have hVariation :
      0 ≤ ∑ k ∈ Finset.range n,
        (w k - w (k + 1)) * phi (k + 1) := by
    apply Finset.sum_nonneg
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    exact mul_nonneg (sub_nonneg.mpr (hMono k hklt))
      (hPhi (k + 1) (by omega))
  have hRemainder :
      0 ≤ ∑ k ∈ Finset.range (n + 1), w k * remainder k := by
    apply Finset.sum_nonneg
    intro k hk
    have hklt : k < n + 1 := Finset.mem_range.mp hk
    exact mul_nonneg (hW k hklt) (hRem k hklt)
  linarith

#print axioms posPart_nonnegative
#print axioms energy_nonnegative
#print axioms jumpRemainder_nonnegative
#print axioms jumpRemainder_le_half_sq
#print axioms one_step_chain
#print axioms weighted_telescope
#print axioms weighted_chain
#print axioms area_budget_le_source

end RHPositiveExcessChain
