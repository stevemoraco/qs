import Mathlib

/-!
# RH B186 E1 endpoint-zero Chebyshev finite core

Finite real/Finset/rational algebra only.

Formalized:

* the weighted endpoint-zero split identity appropriate to Chebyshev weights;
* nonnegativity of a log-weighted future coefficient;
* exact vanishing of the terminal coefficient;
* the two rational inequalities used in the explicit `45.45` tail-reserve ledger.

Not formalized: primes, logarithms as arithmetic data, `theta`, integrals, Zhao,
Johnston--Yang, zeta, B46, BGST, RH, or `not RH`.
-/

namespace RHB186EndpointZeroChebyshevFinite

/-- Exact weighted version of the endpoint-zero split.

`pre` is the already accumulated lower-end weight, `w i` are future atom
weights, `invq i` their reciprocal locations, and `invY` the terminal
reciprocal factor. -/
theorem weighted_endpoint_zero_split_identity
    {ι : Type*} (s : Finset ι) (w invq : ι → ℝ)
    (pre x invY : ℝ) :
    pre + x * (∑ i ∈ s, w i * invq i) -
        x * invY * (pre + ∑ i ∈ s, w i) =
      (1 - x * invY) * pre +
        ∑ i ∈ s, w i * x * (invq i - invY) := by
  have h1 :
      (∑ i ∈ s, w i * x * invq i) =
        x * (∑ i ∈ s, w i * invq i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have h2 :
      (∑ i ∈ s, w i * x * invY) =
        x * invY * (∑ i ∈ s, w i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsum :
      (∑ i ∈ s, w i * x * (invq i - invY)) =
        x * (∑ i ∈ s, w i * invq i) -
          x * invY * (∑ i ∈ s, w i) := by
    calc
      (∑ i ∈ s, w i * x * (invq i - invY)) =
          ∑ i ∈ s, (w i * x * invq i - w i * x * invY) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i ∈ s, w i * x * invq i) -
            (∑ i ∈ s, w i * x * invY) := by
              exact Finset.sum_sub_distrib
      _ = x * (∑ i ∈ s, w i * invq i) -
            x * invY * (∑ i ∈ s, w i) := by rw [h1, h2]
  rw [hsum]
  ring

/-- A nonnegative atom weight times an endpoint-zero future coefficient stays
nonnegative when the atom lies before the terminal horizon. -/
theorem weighted_future_coefficient_nonneg
    {x Y q w : ℝ}
    (hx : 0 ≤ x) (hw : 0 ≤ w)
    (hY : 0 < Y) (hq : 0 < q) (hqY : q ≤ Y) :
    0 ≤ w * (x / q - x / Y) := by
  have hratio : x / Y ≤ x / q := by
    apply (div_le_div_iff₀ hY hq).2
    exact mul_le_mul_of_nonneg_left hqY hx
  exact mul_nonneg hw (sub_nonneg.mpr hratio)

/-- The endpoint-zero weighted future coefficient vanishes exactly at `q=Y`. -/
theorem weighted_future_terminal (x Y w : ℝ) :
    w * (x / Y - x / Y) = 0 := by
  ring

/-- Rational constant ledger behind `4*9.40/0.8274 < 45.45`. -/
theorem tail_reserve_constant_ledger :
    (4 : ℚ) * ((940 : ℚ) / 100) / ((8274 : ℚ) / 10000) <
      (4545 : ℚ) / 100 := by
  norm_num

/-- At `sqrt(log Y) >= 10`, the exponential tail rate retains more than half
of the Johnston--Yang `0.8274` exponent after paying the polynomial envelope. -/
theorem tail_rate_margin_at_ten :
    (8274 : ℚ) / 10000 - (((403 : ℚ) / 100) / 10) >
      ((8274 : ℚ) / 10000) / 2 := by
  norm_num

#print axioms weighted_endpoint_zero_split_identity
#print axioms weighted_future_coefficient_nonneg
#print axioms weighted_future_terminal
#print axioms tail_reserve_constant_ledger
#print axioms tail_rate_margin_at_ten

end RHB186EndpointZeroChebyshevFinite
