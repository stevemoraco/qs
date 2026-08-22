import Mathlib

namespace RHFixedMultiplicativeWindowFinite

/-- A nonnegative fixed-log-window deficit is exactly descent of the
renormalized primitive `I + κL` under `L ↦ L+H`. -/
theorem deficit_nonnegative_iff_renormalized_descent
    (I IR L H κ : ℝ) :
    0 ≤ I - IR - κ * H ↔
      IR + κ * (L + H) ≤ I + κ * L := by
  constructor <;> intro h <;> nlinarith

/-- One fixed multiplicative-window step preserves the renormalized upper
bound. -/
theorem one_step_renormalized_descent
    (I IR L LR H κ : ℝ)
    (hL : LR = L + H)
    (hI : IR ≤ I - κ * H) :
    IR + κ * LR ≤ I + κ * L := by
  rw [hL]
  nlinarith

/-- Finite iteration of a fixed additive step in logarithmic coordinates. -/
theorem iterated_fixed_window_descent
    (I L : ℕ → ℝ) (H κ : ℝ)
    (hL : ∀ n, L (n + 1) = L n + H)
    (hI : ∀ n, I (n + 1) ≤ I n - κ * H) :
    ∀ n, I n + κ * L n ≤ I 0 + κ * L 0 := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      calc
        I (n + 1) + κ * L (n + 1) ≤ I n + κ * L n :=
          one_step_renormalized_descent
            (I n) (I (n + 1)) (L n) (L (n + 1)) H κ
            (hL n) (hI n)
        _ ≤ I 0 + κ * L 0 := ih

/-- A positive logarithmic reserve eventually forces negativity once the
renormalized quantity has a fixed upper bound. -/
theorem renormalized_upper_bound_forces_negative
    (I L κ C : ℝ)
    (hbound : I + κ * L ≤ C)
    (hcross : C < κ * L) :
    I < 0 := by
  linarith

/-- Exact bounded-remainder decomposition of a fixed-window deficit. -/
theorem fixed_window_margin_identity
    (c κ H r₀ r₁ : ℝ) :
    (-c * 0 + r₀) - (-c * H + r₁) - κ * H
      = (c - κ) * H + r₀ - r₁ := by
  ring

/-- Two remainders bounded in absolute value by `B` cannot consume a reserve
larger than `2B`. -/
theorem bounded_remainder_margin_positive
    (c κ H B r₀ r₁ : ℝ)
    (hB : 0 ≤ B)
    (hr₀ : |r₀| ≤ B)
    (hr₁ : |r₁| ≤ B)
    (hreserve : 2 * B < (c - κ) * H) :
    0 < (c - κ) * H + r₀ - r₁ := by
  have hr₀lower : -B ≤ r₀ := (abs_le.mp hr₀).1
  have hr₁upper : r₁ ≤ B := (abs_le.mp hr₁).2
  linarith

/-- A bounded oscillatory remainder places every fixed-window secant inside
an explicit interval around the drift `c`. -/
theorem fixed_window_secant_enclosure
    (c H B r₀ r₁ S : ℝ)
    (hH : 0 < H)
    (hr₀ : |r₀| ≤ B)
    (hr₁ : |r₁| ≤ B)
    (hS : S = (c * H + r₀ - r₁) / H) :
    c - 2 * B / H ≤ S ∧ S ≤ c + 2 * B / H := by
  have hr₀lower : -B ≤ r₀ := (abs_le.mp hr₀).1
  have hr₀upper : r₀ ≤ B := (abs_le.mp hr₀).2
  have hr₁lower : -B ≤ r₁ := (abs_le.mp hr₁).1
  have hr₁upper : r₁ ≤ B := (abs_le.mp hr₁).2
  rw [hS]
  constructor
  · apply (le_div_iff₀ hH).2
    nlinarith
  · apply (div_le_iff₀ hH).2
    nlinarith

/-- A positive lower fixed-window secant supplies a positive deficit reserve. -/
theorem positive_secant_gives_deficit
    (I IR H S κ : ℝ)
    (hH : 0 < H)
    (hS : S = (I - IR) / H)
    (hk : κ ≤ S) :
    0 ≤ I - IR - κ * H := by
  rw [hS] at hk
  have hmul := (le_div_iff₀ hH).mp hk
  linarith

/-- In multiplicative coordinates `R=exp H`, the endpoint is exactly
`R*x = exp (log x + H)`. -/
theorem multiplicative_endpoint_identity
    (x H : ℝ) (hx : 0 < x) :
    Real.exp (Real.log x + H) = Real.exp H * x := by
  rw [Real.exp_add, Real.exp_log hx]

#print axioms deficit_nonnegative_iff_renormalized_descent
#print axioms one_step_renormalized_descent
#print axioms iterated_fixed_window_descent
#print axioms renormalized_upper_bound_forces_negative
#print axioms fixed_window_margin_identity
#print axioms bounded_remainder_margin_positive
#print axioms fixed_window_secant_enclosure
#print axioms positive_secant_gives_deficit
#print axioms multiplicative_endpoint_identity

end RHFixedMultiplicativeWindowFinite
