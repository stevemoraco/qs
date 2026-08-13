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

/-- The normalized identric mean lies below the arithmetic mean by a strict
second-order logarithmic tax. -/
theorem normalized_identric_log_gap_le
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (((1 : ℝ) + t) * Real.log ((1 : ℝ) + t)
        - ((1 : ℝ) - t) * Real.log ((1 : ℝ) - t)) / (2 * t) - 1
      ≤ -(t ^ 2) / 6 := by
  let G : ℝ → ℝ := fun x =>
    ((1 : ℝ) + x) * Real.log ((1 : ℝ) + x)
      - ((1 : ℝ) - x) * Real.log ((1 : ℝ) - x)
      - (2 : ℝ) * x + x ^ 3 / (3 : ℝ)
  have hderiv (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt G (Real.log (1 - x ^ 2) + x ^ 2) x := by
    let p : ℝ → ℝ := fun y => (1 : ℝ) + y
    let n : ℝ → ℝ := fun y => (1 : ℝ) - y
    have hp : p x ≠ 0 := by dsimp [p]; linarith [hx.1]
    have hn : n x ≠ 0 := by dsimp [n]; linarith [hx.2]
    have hp0 : HasDerivAt p 1 x := by
      simpa [p] using (hasDerivAt_id x).const_add (1 : ℝ)
    have hn0 : HasDerivAt n (-1) x := by
      simpa [n] using (hasDerivAt_id x).const_sub (1 : ℝ)
    have hplus := hp0.mul (hp0.log hp)
    have hminus := hn0.mul (hn0.log hn)
    have hlinear := (hasDerivAt_id x).const_mul (2 : ℝ)
    have hcubic := (hasDerivAt_pow 3 x).div_const (3 : ℝ)
    have hraw := ((hplus.sub hminus).sub hlinear).add hcubic
    have hlog : Real.log (1 - x ^ 2) = Real.log (p x) + Real.log (n x) := by
      rw [← Real.log_mul hp hn]
      congr 1
      dsimp [p, n]
      ring
    convert hraw using 1
    · ext y
      simp [G, p, n]
    · rw [hlog]
      dsimp [p, n]
      field_simp [hp, hn]
      ring
  have hcont : ContinuousOn G (Icc 0 t) := by
    intro x hx
    exact (hderiv x ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousAt.continuousWithinAt
  have hanti : AntitoneOn G (Icc 0 t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t) hcont
    · intro x hx
      have hx' : x ∈ Ioo 0 t := by simpa [interior_Icc] using hx
      exact (hderiv x ⟨by linarith [hx'.1], by linarith [hx'.2]⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ioo 0 t := by simpa [interior_Icc] using hx
      have hxdom : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
      rw [(hderiv x hxdom).deriv]
      have hpos : 0 < 1 - x ^ 2 := by nlinarith [sq_nonneg x, hxdom.1, hxdom.2]
      have hlog := Real.log_le_sub_one_of_pos hpos
      nlinarith
  have hG := hanti (by simp [ht0.le]) (by simp [ht0.le]) ht0.le
  have hG0 : G 0 = 0 := by simp [G]
  rw [hG0] at hG
  rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
  dsimp [G] at hG
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

#print axioms normalized_identric_log_gap_le
#print axioms exp_neg_le_one_div_one_add
#print axioms positive_arrival_forces_reserve_tax
#print axioms positive_arrival_narrows_half_atom_window

end
end RHIdentricReserveTax
end MillenniumBraid
