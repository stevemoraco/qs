import Mathlib

/-!
# Two-tap autocorrelation profile cone

This file formalizes only the smallest finite scalar shadow of an identical-
envelope recursive packet lift. For a real two-tap cell `(x,y)`, the cyclic
autocorrelation data are

`A = x^2 + y^2`, `B = 2*x*y`.

The file proves the exact range characterization, an impossible target, and
an exact boundary realization. It does not formalize Fourier transforms,
Gaussian packets, Leray projection, Navier--Stokes evolution, or blow-up.
-/

namespace NSTwoTapAutocorrelation

noncomputable section

/-- Zero-lag cyclic autocorrelation of a two-tap real cell. -/
def lagZero (x y : ℝ) : ℝ := x ^ 2 + y ^ 2

/-- Nonzero-lag cyclic autocorrelation of a two-tap real cell. -/
def lagOne (x y : ℝ) : ℝ := 2 * x * y

/-- BANKER: the two endpoint Fourier channels are exact squares. -/
theorem autocorrelation_endpoints_are_squares (x y : ℝ) :
    lagZero x y + lagOne x y = (x + y) ^ 2 ∧
      lagZero x y - lagOne x y = (x - y) ^ 2 := by
  unfold lagZero lagOne
  constructor <;> ring

/-- Every two-tap self-correlation has nonnegative endpoint Fourier channels. -/
theorem autocorrelation_endpoints_nonnegative (x y : ℝ) :
    0 ≤ lagZero x y + lagOne x y ∧
      0 ≤ lagZero x y - lagOne x y := by
  have h := autocorrelation_endpoints_are_squares x y
  constructor
  · rw [h.1]
    exact sq_nonneg _
  · rw [h.2]
    exact sq_nonneg _

/-- Equivalently, the nonzero lag cannot exceed the zero lag in magnitude. -/
theorem autocorrelation_lag_bound (x y : ℝ) :
    |lagOne x y| ≤ lagZero x y := by
  rw [abs_le]
  constructor
  · have h := (autocorrelation_endpoints_nonnegative x y).1
    linarith
  · have h := (autocorrelation_endpoints_nonnegative x y).2
    linarith

/-- CLEANER: exact range characterization of the two-tap cyclic
self-correlation map. -/
theorem two_tap_autocorrelation_characterization (A B : ℝ) :
    (∃ x y : ℝ, lagZero x y = A ∧ lagOne x y = B) ↔
      0 ≤ A + B ∧ 0 ≤ A - B := by
  constructor
  · rintro ⟨x, y, hA, hB⟩
    have h := autocorrelation_endpoints_nonnegative x y
    rw [hA, hB] at h
    exact h
  · rintro ⟨hplus, hminus⟩
    let u := Real.sqrt (A + B)
    let v := Real.sqrt (A - B)
    have hu : u ^ 2 = A + B := by
      dsimp [u]
      exact Real.sq_sqrt hplus
    have hv : v ^ 2 = A - B := by
      dsimp [v]
      exact Real.sq_sqrt hminus
    refine ⟨(u + v) / 2, (u - v) / 2, ?_, ?_⟩
    · unfold lagZero
      nlinarith
    · unfold lagOne
      nlinarith

/-- CRITIC: the target with zero lag one and nonzero lag two is outside the
self-correlation cone. -/
theorem target_one_two_is_impossible :
    ¬ ∃ x y : ℝ, lagZero x y = 1 ∧ lagOne x y = 2 := by
  intro h
  have hrange := (two_tap_autocorrelation_characterization 1 2).1 h
  norm_num at hrange

/-- The positive-definite boundary is genuinely attainable. -/
theorem equal_lag_boundary_is_realizable :
    lagZero 1 1 = 2 ∧ lagOne 1 1 = 2 := by
  norm_num [lagZero, lagOne]

#print axioms autocorrelation_endpoints_are_squares
#print axioms autocorrelation_endpoints_nonnegative
#print axioms autocorrelation_lag_bound
#print axioms two_tap_autocorrelation_characterization
#print axioms target_one_two_is_impossible
#print axioms equal_lag_boundary_is_realizable

end

end NSTwoTapAutocorrelation
