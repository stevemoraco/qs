import Mathlib

/-!
# RH identric-arrival second-order reserve tax

HONESTY BOUNDARY

This file formalizes the analytic scalar inequality behind a sharpening of the
Fenchel/identric prime-arrival gate:

* the centered identric logarithmic gap is at most `-t^2 / 6` for `0<t<1`;
* an identric upper envelope together with a positive arrival forces a strict
  quantitative reserve tax;
* the tax strictly narrows the arithmetic-mean half-atom danger strip.

It does not formalize primes, the von Mangoldt function, Chebyshev functions,
Suzuki's criterion, zeta zeros, or the Riemann Hypothesis.
-/

namespace MillenniumBraid
namespace RHIdentricReserveTax

open Set

noncomputable section

/-- The numerator form whose sign is equivalent to the quadratic identric
log-gap estimate. -/
def identricGapPrimitive : ℝ → ℝ :=
  (fun t => (t + 1) * Real.log (t + 1))
    - (fun t => (1 - t) * Real.log (1 - t))
    - (fun t => 2 * t)
    + (fun t => t ^ 3 / 3)

/-- Exact derivative of the identric gap primitive on `(-1,1)`. -/
lemma hasDerivAt_identricGapPrimitive
    {t : ℝ} (htm : -1 < t) (htp : t < 1) :
    HasDerivAt identricGapPrimitive (Real.log (1 - t ^ 2) + t ^ 2) t := by
  have hp : t + 1 ≠ 0 := by linarith
  have hm : 1 - t ≠ 0 := by linarith
  have hplus0 : HasDerivAt (fun x : ℝ => x + 1) 1 t :=
    (hasDerivAt_id t).const_add 1
  have hminus0 : HasDerivAt (fun x : ℝ => 1 - x) (-1) t :=
    (hasDerivAt_id t).const_sub 1
  have hplus :
      HasDerivAt (fun x : ℝ => (x + 1) * Real.log (x + 1))
        (Real.log (t + 1) + 1) t := by
    simpa [hp] using hplus0.mul (hplus0.log hp)
  have hminus :
      HasDerivAt (fun x : ℝ => (1 - x) * Real.log (1 - x))
        (-Real.log (1 - t) - 1) t := by
    simpa [hm] using hminus0.mul (hminus0.log hm)
  have hlinear : HasDerivAt (fun x : ℝ => 2 * x) 2 t := by
    simpa using (hasDerivAt_id t).const_mul 2
  have hcubic : HasDerivAt (fun x : ℝ => x ^ 3 / 3) (t ^ 2) t := by
    convert ((hasDerivAt_id t).pow 3).div_const 3 using 1
    · rfl
    · ring
  have h := (hplus.sub hminus).sub hlinear |>.add hcubic
  have hlog : Real.log (1 - t ^ 2) = Real.log (t + 1) + Real.log (1 - t) := by
    rw [← Real.log_mul hp hm]
    congr 1
    ring
  simpa only [identricGapPrimitive, hlog] using h

/-- On `[0,1)`, the primitive is nonpositive.  The proof uses only
`log z ≤ z-1` at `z=1-t^2`. -/
lemma identricGapPrimitive_nonpos
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    identricGapPrimitive t ≤ 0 := by
  have hcont : ContinuousOn identricGapPrimitive (Icc 0 t) := by
    intro x hx
    exact (hasDerivAt_identricGapPrimitive (by linarith [hx.1])
      (by linarith [hx.2])).continuousAt.continuousWithinAt
  have hanti : AntitoneOn identricGapPrimitive (Icc 0 t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t) hcont
    · intro x hx
      have hx' : x ∈ Ioo 0 t := by simpa [interior_Icc] using hx
      exact (hasDerivAt_identricGapPrimitive (by linarith [hx'.1])
        (by linarith [hx'.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ioo 0 t := by simpa [interior_Icc] using hx
      have hx0 : 0 < x := hx'.1
      have hx1 : x < 1 := hx'.2.trans ht1
      rw [(hasDerivAt_identricGapPrimitive (by linarith) hx1).deriv]
      have hpos : 0 < 1 - x ^ 2 := by nlinarith [sq_nonneg x]
      have hlog := Real.log_le_sub_one_of_pos hpos
      nlinarith
  have h := hanti (by simp [ht0]) (by simp [ht0]) ht0
  simpa [identricGapPrimitive] using h

/-- The normalized identric mean lies below the arithmetic mean by a strict
second-order logarithmic tax. -/
theorem normalized_identric_log_gap_le
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ((t + 1) * Real.log (t + 1)
        - (1 - t) * Real.log (1 - t)) / (2 * t) - 1
      ≤ -(t ^ 2) / 6 := by
  have h := identricGapPrimitive_nonpos ht0.le ht1
  rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
  simp only [identricGapPrimitive, Pi.sub_apply, Pi.add_apply] at h
  nlinarith

/-- Elementary exponential conversion: a logarithmic tax `z` forces the
relative linear loss `z/(1+z)`. -/
lemma exp_neg_le_one_div_one_add
    {z : ℝ} (hz : 0 ≤ z) :
    Real.exp (-z) ≤ 1 / (1 + z) := by
  have hpos : 0 < 1 + z := by linarith
  have hexp : 1 + z ≤ Real.exp z := by
    simpa [add_comm] using Real.add_one_le_exp z
  have hinv : (Real.exp z)⁻¹ ≤ (1 + z)⁻¹ :=
    (inv_le_inv₀ (by positivity) hpos).2 hexp
  simpa [Real.exp_neg, one_div] using hinv

/-- Generic reserve-tax consequence.  If a positive arrival threshold `H` is
strictly below a quantity `I`, while `I` is bounded by
`m * exp(-a^2/(24m^2))`, then the midpoint excess `m-H` pays a strict
rational tax. -/
theorem positive_arrival_forces_reserve_tax
    {H a m I : ℝ}
    (hH : 0 < H) (ha : 0 < a) (hm : H < m)
    (hI : H < I)
    (hupper : I ≤ m * Real.exp (-(a ^ 2 / (24 * m ^ 2)))) :
    a ^ 2 * m / (24 * m ^ 2 + a ^ 2) < m - H := by
  have hm0 : 0 < m := hH.trans hm
  let z : ℝ := a ^ 2 / (24 * m ^ 2)
  have hz : 0 ≤ z := by
    dsimp [z]
    positivity
  have hden : 0 < 1 + z := by linarith
  have hHm : H < m * Real.exp (-z) := lt_of_lt_of_le hI hupper
  have hbound : H < m / (1 + z) := by
    calc
      H < m * Real.exp (-z) := hHm
      _ ≤ m * (1 / (1 + z)) := by
        gcongr
        exact exp_neg_le_one_div_one_add hz
      _ = m / (1 + z) := by ring
  dsimp [z] at hbound ⊢
  field_simp [ne_of_gt hm0, ne_of_gt hden] at hbound ⊢
  nlinarith [sq_pos_of_pos ha]

/-- In the pre-crossing regime `R = H-x > 0`, a positive identric arrival
forces a strict improvement over the half-atom window `R<a/2`. -/
theorem positive_arrival_narrows_half_atom_window
    {H a R m I : ℝ}
    (hH : 0 < H) (ha : 0 < a)
    (hmdef : m = H + a / 2 - R)
    (hm : H < m) (hI : H < I)
    (hupper : I ≤ m * Real.exp (-(a ^ 2 / (24 * m ^ 2)))) :
    R < a / 2 - a ^ 2 * m / (24 * m ^ 2 + a ^ 2) := by
  have htax := positive_arrival_forces_reserve_tax hH ha hm hI hupper
  rw [hmdef] at htax ⊢
  linarith

#print axioms hasDerivAt_identricGapPrimitive
#print axioms identricGapPrimitive_nonpos
#print axioms normalized_identric_log_gap_le
#print axioms exp_neg_le_one_div_one_add
#print axioms positive_arrival_forces_reserve_tax
#print axioms positive_arrival_narrows_half_atom_window

end
end RHIdentricReserveTax
end MillenniumBraid
