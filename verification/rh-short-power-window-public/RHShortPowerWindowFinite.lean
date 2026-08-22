import Mathlib

namespace RHShortPowerWindowFinite

/-- Exact algebraic equivalence between a nonnegative power-window deficit and
monotonicity of the renormalized state `I + κ L` under `L ↦ qL`. -/
theorem deficit_nonnegative_iff_renormalized_descent
    (I Iq L q κ : ℝ) :
    0 ≤ I - Iq - κ * (q - 1) * L ↔
      Iq + κ * (q * L) ≤ I + κ * L := by
  constructor <;> intro h <;> nlinarith

/-- One power-window step preserves the upper bound for the renormalized
quantity. No positivity assumption is needed for this finite algebraic step. -/
theorem one_step_renormalized_descent
    (I Iq L Lq q κ : ℝ)
    (hL : Lq = q * L)
    (hI : Iq ≤ I - κ * (q - 1) * L) :
    Iq + κ * Lq ≤ I + κ * L := by
  rw [hL]
  nlinarith

/-- Finite iteration of the renormalized power-window descent. -/
theorem iterated_renormalized_descent
    (I L : ℕ → ℝ) (q κ : ℝ)
    (hL : ∀ n, L (n + 1) = q * L n)
    (hI : ∀ n, I (n + 1) ≤ I n - κ * (q - 1) * L n) :
    ∀ n, I n + κ * L n ≤ I 0 + κ * L 0 := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      calc
        I (n + 1) + κ * L (n + 1) ≤ I n + κ * L n :=
          one_step_renormalized_descent
            (I n) (I (n + 1)) (L n) (L (n + 1)) q κ
            (hL n) (hI n)
        _ ≤ I 0 + κ * L 0 := ih

/-- Once the logarithmic coordinate is larger than the fixed renormalized
upper bound divided by a positive reserve, the primitive is negative. -/
theorem renormalized_bound_forces_negative
    (I L κ C : ℝ)
    (hbound : I + κ * L ≤ C)
    (hcross : C < κ * L) :
    I < 0 := by
  linarith

/-- Exact asymptotic-error bookkeeping for a fixed power window. -/
theorem power_window_margin_identity
    (c κ q L e₀ e₁ : ℝ) :
    (-c * L + e₀) - (-c * (q * L) + e₁) - κ * (q - 1) * L
      = (c - κ) * (q - 1) * L + e₀ - e₁ := by
  ring

/-- The deterministic power-window margin is positive when `q>1`, `c>κ`,
and the logarithmic coordinate is positive. -/
theorem power_window_margin_positive
    (c κ q L : ℝ)
    (hck : κ < c)
    (hq : 1 < q)
    (hL : 0 < L) :
    0 < (c - κ) * (q - 1) * L := by
  have h₁ : 0 < c - κ := sub_pos.mpr hck
  have h₂ : 0 < q - 1 := sub_pos.mpr hq
  positivity

/-- Substituting `q=1+ε` turns the power-window logarithmic reserve into the
exact short-window reserve `κ ε L`. -/
theorem epsilon_window_reserve_identity
    (κ ε L : ℝ) :
    κ * ((1 + ε) - 1) * L = κ * ε * L := by
  ring

/-- A positive normalized secant lower bound supplies a fixed positive reserve. -/
theorem normalized_secant_gives_deficit
    (I Iq denom R κ : ℝ)
    (hdenom : 0 < denom)
    (hR : R = (I - Iq) / denom)
    (hk : κ ≤ R) :
    0 ≤ I - Iq - κ * denom := by
  rw [hR] at hk
  have hmul := (le_div_iff₀ hdenom).mp hk
  linarith

/-- Zero logarithmic reserve is logically insufficient: the positive function
`J(L)=1+exp(-L)` strictly decreases under every dilation `L ↦ qL` while
remaining positive. -/
theorem zero_reserve_countermodel
    (q L : ℝ)
    (hq : 1 < q)
    (hL : 0 < L) :
    0 < 1 + Real.exp (-L) ∧
      1 + Real.exp (-(q * L)) < 1 + Real.exp (-L) := by
  constructor
  · positivity
  · have harg : -(q * L) < -L := by
      nlinarith
    have hexp : Real.exp (-(q * L)) < Real.exp (-L) :=
      Real.exp_lt_exp.mpr harg
    linarith

#print axioms deficit_nonnegative_iff_renormalized_descent
#print axioms one_step_renormalized_descent
#print axioms iterated_renormalized_descent
#print axioms renormalized_bound_forces_negative
#print axioms power_window_margin_identity
#print axioms power_window_margin_positive
#print axioms epsilon_window_reserve_identity
#print axioms normalized_secant_gives_deficit
#print axioms zero_reserve_countermodel

end RHShortPowerWindowFinite
