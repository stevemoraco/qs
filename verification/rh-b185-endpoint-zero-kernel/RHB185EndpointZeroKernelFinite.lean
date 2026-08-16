import Mathlib

/-!
# RH B185 endpoint-zero weighted-kernel finite core

Finite real/Finset algebra only.

This file formalizes the load-bearing new algebra behind RH B185:

* the old-prime coefficient `1 - x/Y` is nonnegative for `x <= Y`;
* the future-prime coefficient `x/q - x/Y` is nonnegative for `0 <= x`,
  `0 < q <= Y`;
* the future coefficient vanishes exactly at the terminal endpoint `q = Y`;
* a count plus a reciprocal-weighted future sum, after subtracting the terminal
  count coefficient, is exactly one endpoint-zero weighted sum.

It does **not** formalize primes, `li`, integration, Zhao, Johnston--Yang, zeta,
BGST, B46, or RH.
-/

namespace RHB185EndpointZeroKernelFinite

/-- The weight carried by an atom at or below the lower endpoint. -/
def oldWeight (x Y : ℝ) : ℝ := 1 - x / Y

/-- The weight carried by an atom strictly above the lower endpoint. -/
def futureWeight (x Y q : ℝ) : ℝ := x / q - x / Y

/-- The old-atom weight is nonnegative when the horizon lies to the right. -/
theorem oldWeight_nonneg
    {x Y : ℝ} (hY : 0 < Y) (hxy : x ≤ Y) :
    0 ≤ oldWeight x Y := by
  have hdiv : x / Y ≤ 1 := (div_le_one hY).2 hxy
  dsimp [oldWeight]
  linarith

/-- A future-atom weight is nonnegative on `q <= Y`. -/
theorem futureWeight_nonneg
    {x Y q : ℝ}
    (hx : 0 ≤ x) (hY : 0 < Y) (hq : 0 < q) (hqY : q ≤ Y) :
    0 ≤ futureWeight x Y q := by
  have hratio : x / Y ≤ x / q := by
    apply (div_le_div_iff₀ hY hq).2
    exact mul_le_mul_of_nonneg_left hqY hx
  dsimp [futureWeight]
  linarith

/-- The endpoint-zero normalization kills the terminal coefficient exactly. -/
@[simp] theorem futureWeight_terminal (x Y : ℝ) :
    futureWeight x Y Y = 0 := by
  simp [futureWeight]

/-- Exact finite algebra behind the B185 single weighted-prime sum.

`pre` is the lower-end prime count, `r i` are the future reciprocal weights,
and `invY` is the terminal reciprocal factor.  Subtracting the terminal count
coefficient converts the split count/reciprocal expression into one weighted
sum whose future coefficient is `x * (r i - invY)`. -/
theorem endpoint_zero_split_identity
    {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (pre x invY : ℝ) :
    pre + x * (∑ i ∈ s, r i) - x * invY * (pre + (s.card : ℝ)) =
      (1 - x * invY) * pre +
        ∑ i ∈ s, x * (r i - invY) := by
  have hsum :
      (∑ i ∈ s, x * (r i - invY)) =
        x * (∑ i ∈ s, r i) - (s.card : ℝ) * (x * invY) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    simp
  rw [hsum]
  ring

/-- Scalar monotonicity firewall: omitted nonnegative endpoint-zero prime mass
can only increase the exact full weighted prime sum. -/
theorem omitted_nonnegative_weight_is_safe
    {subtotal omitted : ℝ} (homitted : 0 ≤ omitted) :
    subtotal ≤ subtotal + omitted := by
  linarith

#print axioms oldWeight_nonneg
#print axioms futureWeight_nonneg
#print axioms futureWeight_terminal
#print axioms endpoint_zero_split_identity
#print axioms omitted_nonnegative_weight_is_safe

end RHB185EndpointZeroKernelFinite
