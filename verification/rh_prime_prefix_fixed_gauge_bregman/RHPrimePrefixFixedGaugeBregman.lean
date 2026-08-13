import Mathlib

namespace RHPrimePrefixFixedGaugeBregman

/-- Linearizes one equal-square increment around a nonzero base point. -/
theorem square_increment_linearization
    {u U t : ℝ}
    (hU : U ≠ 0)
    (htu : t = (u - U) * (u + U)) :
    t / U = 2 * (u - U) + (u - U) ^ 2 / U := by
  rw [htu]
  field_simp [hU]
  ring

/-- Rewrites the exact second-order remainder of one equal-square increment. -/
theorem square_increment_remainder
    {u U t : ℝ}
    (hU : U ≠ 0)
    (huU : u + U ≠ 0)
    (htu : t = (u - U) * (u + U)) :
    t ^ 2 / (U * (u + U) ^ 2) = (u - U) ^ 2 / U := by
  rw [htu]
  field_simp [hU, huU]

/-- Exact two-root Bregman identity.  It is the finite algebra behind the
fixed-gauge prime-prefix decomposition. -/
theorem fixed_tangent_bregman_identity
    {u v U V t : ℝ}
    (hU : U ≠ 0)
    (hV : V ≠ 0)
    (huU : u + U ≠ 0)
    (hvV : v + V ≠ 0)
    (htu : t = (u - U) * (u + U))
    (htv : t = (v - V) * (v + V)) :
    2 * ((u - v) - (U - V)) - (1 / U - 1 / V) * t =
      t ^ 2 *
        (1 / (V * (v + V) ^ 2) - 1 / (U * (u + U) ^ 2)) := by
  have hu := square_increment_linearization hU htu
  have hv := square_increment_linearization hV htv
  have hru := square_increment_remainder hU huU htu
  have hrv := square_increment_remainder hV hvV htv
  calc
    2 * ((u - v) - (U - V)) - (1 / U - 1 / V) * t =
        2 * ((u - U) - (v - V)) - (t / U - t / V) := by ring
    _ = (v - V) ^ 2 / V - (u - U) ^ 2 / U := by
      rw [hu, hv]
      ring
    _ = t ^ 2 / (V * (v + V) ^ 2) -
        t ^ 2 / (U * (u + U) ^ 2) := by
      rw [← hrv, ← hru]
    _ = t ^ 2 *
        (1 / (V * (v + V) ^ 2) - 1 / (U * (u + U) ^ 2)) := by
      ring

/-- On the physical ordered-root domain, the Bregman bracket is strictly
positive. -/
theorem reciprocal_remainder_positive
    {u v U V : ℝ}
    (hV : 0 < V)
    (hVU : V < U)
    (hv : 0 < v)
    (hvu : v < u) :
    0 < 1 / (V * (v + V) ^ 2) - 1 / (U * (u + U) ^ 2) := by
  have hU : 0 < U := lt_trans hV hVU
  have hu : 0 < u := lt_trans hv hvu
  have hsumV : 0 < v + V := add_pos hv hV
  have hsumU : 0 < u + U := add_pos hu hU
  have hsum : v + V < u + U := add_lt_add hvu hVU
  have hsquares : (v + V) ^ 2 < (u + U) ^ 2 := by
    nlinarith
  have hdenV : 0 < V * (v + V) ^ 2 :=
    mul_pos hV (sq_pos_of_pos hsumV)
  have hdenU : 0 < U * (u + U) ^ 2 :=
    mul_pos hU (sq_pos_of_pos hsumU)
  have hden : V * (v + V) ^ 2 < U * (u + U) ^ 2 := by
    calc
      V * (v + V) ^ 2 < U * (v + V) ^ 2 :=
        mul_lt_mul_of_pos_right hVU (sq_pos_of_pos hsumV)
      _ < U * (u + U) ^ 2 :=
        mul_lt_mul_of_pos_left hsquares hU
  have hrecip : 1 / (U * (u + U) ^ 2) < 1 / (V * (v + V) ^ 2) := by
    apply (div_lt_div_iff₀ hdenU hdenV).2
    nlinarith
  exact sub_pos.mpr hrecip

/-- The threshold-excess coordinate turns the tangent term into one fixed
coefficient times the excess. -/
theorem threshold_excess_linear_term
    {H L U V t c : ℝ}
    (ht : t = -H / L)
    (hc : c = (1 / L) * (1 / V - 1 / U)) :
    (1 / U - 1 / V) * t = c * H := by
  rw [ht, hc]
  ring

/-- Exact fixed-gauge decomposition of the nonlinear root increment. -/
theorem fixed_gauge_bregman_decomposition
    {u v U V t H L c : ℝ}
    (hU : U ≠ 0)
    (hV : V ≠ 0)
    (huU : u + U ≠ 0)
    (hvV : v + V ≠ 0)
    (htu : t = (u - U) * (u + U))
    (htv : t = (v - V) * (v + V))
    (ht : t = -H / L)
    (hc : c = (1 / L) * (1 / V - 1 / U)) :
    2 * ((u - v) - (U - V)) =
      c * H + t ^ 2 *
        (1 / (V * (v + V) ^ 2) - 1 / (U * (u + U) ^ 2)) := by
  have hid := fixed_tangent_bregman_identity hU hV huU hvV htu htv
  have hlin := threshold_excess_linear_term ht hc
  linarith

/-- The nonlinear increment dominates its fixed tangent on the physical
ordered-root domain. -/
theorem fixed_gauge_tangent_domination
    {u v U V t H L c : ℝ}
    (hU : U ≠ 0)
    (hV : V ≠ 0)
    (huU : u + U ≠ 0)
    (hvV : v + V ≠ 0)
    (htu : t = (u - U) * (u + U))
    (htv : t = (v - V) * (v + V))
    (ht : t = -H / L)
    (hc : c = (1 / L) * (1 / V - 1 / U))
    (hVpos : 0 < V)
    (hVU : V < U)
    (hvpos : 0 < v)
    (hvu : v < u) :
    c * H ≤ 2 * ((u - v) - (U - V)) := by
  have hdecomp := fixed_gauge_bregman_decomposition
    hU hV huU hvV htu htv ht hc
  have hbracket := reciprocal_remainder_positive hVpos hVU hvpos hvu
  have hrem : 0 ≤ t ^ 2 *
      (1 / (V * (v + V) ^ 2) - 1 / (U * (u + U) ^ 2)) :=
    mul_nonneg (sq_nonneg t) (le_of_lt hbracket)
  linarith

/-- Closed form of the prime-dependent but state-independent tangent weight. -/
theorem fixed_weight_closed_form
    {r L : ℝ}
    (hr : r ≠ 0)
    (hL : L ≠ 0)
    (hminus : 4 * r ^ 2 - L ≠ 0)
    (hplus : 4 * r ^ 2 + L ≠ 0)
    (hden : 16 * r ^ 4 - L ^ 2 ≠ 0) :
    (1 / L) *
        (1 / (r - L / (4 * r)) - 1 / (r + L / (4 * r))) =
      8 * r / (16 * r ^ 4 - L ^ 2) := by
  have hminus_rewrite :
      1 / (r - L / (4 * r)) = 4 * r / (4 * r ^ 2 - L) := by
    field_simp [hr, hminus]
    ring
  have hplus_rewrite :
      1 / (r + L / (4 * r)) = 4 * r / (4 * r ^ 2 + L) := by
    field_simp [hr, hplus]
    ring
  rw [hminus_rewrite, hplus_rewrite]
  field_simp [hL, hminus, hplus, hden]
  ring

/-- The closed tangent weight is positive on the prime-like domain
`r>0`, `0<L<4r^2`. -/
theorem fixed_weight_positive
    {r L : ℝ}
    (hr : 0 < r)
    (hL : 0 < L)
    (hsmall : L < 4 * r ^ 2) :
    0 < 8 * r / (16 * r ^ 4 - L ^ 2) := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hleft : 0 < 4 * r ^ 2 - L := sub_pos.mpr hsmall
  have hright : 0 < 4 * r ^ 2 + L :=
    add_pos (mul_pos (by norm_num) hr2) hL
  have hden : 0 < 16 * r ^ 4 - L ^ 2 := by
    calc
      16 * r ^ 4 - L ^ 2 =
          (4 * r ^ 2 - L) * (4 * r ^ 2 + L) := by ring
      _ > 0 := mul_pos hleft hright
  exact div_pos (mul_pos (by norm_num) hr) hden

/-- Exact finite ledger obtained by summing fixed-gauge decompositions. -/
theorem finite_fixed_gauge_ledger
    {n : ℕ}
    (increment linear remainder : Fin n → ℝ)
    (hdecomp : ∀ i, increment i = linear i + remainder i) :
    (∑ i, increment i) = (∑ i, linear i) + ∑ i, remainder i := by
  calc
    (∑ i, increment i) = ∑ i, (linear i + remainder i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hdecomp i
    _ = (∑ i, linear i) + ∑ i, remainder i := by
      exact Finset.sum_add_distrib

/-- Nonnegative local Bregman remainders give a finite global lower bound. -/
theorem finite_fixed_gauge_domination
    {n : ℕ}
    (increment linear remainder : Fin n → ℝ)
    (hdecomp : ∀ i, increment i = linear i + remainder i)
    (hrem : ∀ i, 0 ≤ remainder i) :
    (∑ i, linear i) ≤ ∑ i, increment i := by
  apply Finset.sum_le_sum
  intro i hi
  rw [hdecomp i]
  exact le_add_of_nonneg_right (hrem i)

#print axioms square_increment_linearization
#print axioms square_increment_remainder
#print axioms fixed_tangent_bregman_identity
#print axioms reciprocal_remainder_positive
#print axioms threshold_excess_linear_term
#print axioms fixed_gauge_bregman_decomposition
#print axioms fixed_gauge_tangent_domination
#print axioms fixed_weight_closed_form
#print axioms fixed_weight_positive
#print axioms finite_fixed_gauge_ledger
#print axioms finite_fixed_gauge_domination

end RHPrimePrefixFixedGaugeBregman
