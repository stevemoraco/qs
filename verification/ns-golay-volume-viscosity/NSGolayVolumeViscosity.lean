import Mathlib

/-!
# Volume--viscosity cubic ceiling: finite scalar core

This file formalizes only the elimination of packet volume, angular
separation, and high-shell frequency from four scalar inequalities:

* a target coefficient lies below the actual coefficient;
* concentration bounds coefficient square by `r^2 V`;
* an uncancelled return obeys `r V <= epsilon nu N theta^2`;
* viscous high-shell growth requires `nu N^2 <= c A`.

It does not formalize Fourier packet estimates, Palasek trapping,
Navier--Stokes evolution, shadowing, or blow-up.
-/

namespace NSGolayVolumeViscosity

/-- BANKER: concentration plus an uncancelled return budget eliminates `V`
and `theta`, giving a quadratic coefficient bound. -/
theorem active_return_gives_quadratic_ceiling
    (cStar c r V epsilon nu N theta : ℝ)
    (hcStar : 0 ≤ cStar) (hr : 0 ≤ r)
    (hepsilon : 0 ≤ epsilon) (hnu : 0 ≤ nu) (hN : 0 ≤ N)
    (hcoeff : cStar ≤ c)
    (hactive : c ^ 2 ≤ r ^ 2 * V)
    (hreturn : r * V ≤ epsilon * nu * N * theta ^ 2)
    (htheta : theta ^ 2 ≤ 1) :
    cStar ^ 2 ≤ r * epsilon * nu * N := by
  have hc : 0 ≤ c := le_trans hcStar hcoeff
  have hsqdiff : 0 ≤ (c - cStar) * (c + cStar) :=
    mul_nonneg (sub_nonneg.mpr hcoeff) (add_nonneg hc hcStar)
  have hcoeffSq : cStar ^ 2 ≤ c ^ 2 := by
    nlinarith
  have hfactor : 0 ≤ epsilon * nu * N := by positivity
  have hthetaScaled :
      epsilon * nu * N * theta ^ 2 ≤ epsilon * nu * N := by
    calc
      epsilon * nu * N * theta ^ 2 =
          (epsilon * nu * N) * theta ^ 2 := by ring
      _ ≤ (epsilon * nu * N) * 1 :=
        mul_le_mul_of_nonneg_left htheta hfactor
      _ = epsilon * nu * N := by ring
  have hreturnLinear : r * V ≤ epsilon * nu * N :=
    le_trans hreturn hthetaScaled
  have hreturnScaled := mul_le_mul_of_nonneg_left hreturnLinear hr
  calc
    cStar ^ 2 ≤ c ^ 2 := hcoeffSq
    _ ≤ r ^ 2 * V := hactive
    _ = r * (r * V) := by ring
    _ ≤ r * (epsilon * nu * N) := hreturnScaled
    _ = r * epsilon * nu * N := by ring

/-- CLEANER: adding the viscous growth gate and a fixed relative coefficient
window gives the exact cubic ceiling. -/
theorem cubic_coefficient_ceiling
    (cStar c K r epsilon nu N A : ℝ)
    (hcStar : 0 < cStar)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hepsilon : 0 ≤ epsilon)
    (hnu : 0 ≤ nu) (hN : 0 ≤ N) (hA : 0 ≤ A)
    (hquad : cStar ^ 2 ≤ r * epsilon * nu * N)
    (hgrowth : nu * N ^ 2 ≤ c * A)
    (hupper : c ≤ K * cStar) :
    cStar ^ 3 ≤ K * r ^ 2 * epsilon ^ 2 * nu * A := by
  let B : ℝ := r * epsilon * nu * N
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hcStarSq : 0 ≤ cStar ^ 2 := sq_nonneg cStar
  have hdiff : 0 ≤ B - cStar ^ 2 := sub_nonneg.mpr hquad
  have hsum : 0 ≤ B + cStar ^ 2 := add_nonneg hB hcStarSq
  have hprod : 0 ≤ (B - cStar ^ 2) * (B + cStar ^ 2) :=
    mul_nonneg hdiff hsum
  have hsquare : cStar ^ 4 ≤ B ^ 2 := by
    nlinarith
  have hnuGrowth : nu ^ 2 * N ^ 2 ≤ nu * c * A := by
    calc
      nu ^ 2 * N ^ 2 = nu * (nu * N ^ 2) := by ring
      _ ≤ nu * (c * A) := mul_le_mul_of_nonneg_left hgrowth hnu
      _ = nu * c * A := by ring
  have hscaleNonneg : 0 ≤ r ^ 2 * epsilon ^ 2 :=
    mul_nonneg (sq_nonneg r) (sq_nonneg epsilon)
  have hscaled := mul_le_mul_of_nonneg_left hnuGrowth hscaleNonneg
  have hmiddle : B ^ 2 ≤ r ^ 2 * epsilon ^ 2 * nu * c * A := by
    dsimp [B]
    calc
      (r * epsilon * nu * N) ^ 2 =
          (r ^ 2 * epsilon ^ 2) * (nu ^ 2 * N ^ 2) := by ring
      _ ≤ (r ^ 2 * epsilon ^ 2) * (nu * c * A) := hscaled
      _ = r ^ 2 * epsilon ^ 2 * nu * c * A := by ring
  have hupperFactor : 0 ≤ r ^ 2 * epsilon ^ 2 * nu * A := by positivity
  have hupperScaled := mul_le_mul_of_nonneg_left hupper hupperFactor
  have hfourth :
      cStar ^ 4 ≤ K * r ^ 2 * epsilon ^ 2 * nu * A * cStar := by
    calc
      cStar ^ 4 ≤ B ^ 2 := hsquare
      _ ≤ r ^ 2 * epsilon ^ 2 * nu * c * A := hmiddle
      _ = (r ^ 2 * epsilon ^ 2 * nu * A) * c := by ring
      _ ≤ (r ^ 2 * epsilon ^ 2 * nu * A) * (K * cStar) :=
        hupperScaled
      _ = K * r ^ 2 * epsilon ^ 2 * nu * A * cStar := by ring
  have hmul :
      cStar ^ 3 * cStar ≤
        (K * r ^ 2 * epsilon ^ 2 * nu * A) * cStar := by
    nlinarith
  exact (mul_le_mul_right hcStar).mp hmul

/-- BANKER: the full packet hypotheses imply the cubic ceiling directly. -/
theorem full_uncancelled_route_cubic_ceiling
    (cStar c K r V epsilon nu N theta A : ℝ)
    (hcStar : 0 < cStar)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hepsilon : 0 ≤ epsilon)
    (hnu : 0 ≤ nu) (hN : 0 ≤ N) (hA : 0 ≤ A)
    (hcoeffLow : cStar ≤ c) (hcoeffHigh : c ≤ K * cStar)
    (hactive : c ^ 2 ≤ r ^ 2 * V)
    (hreturn : r * V ≤ epsilon * nu * N * theta ^ 2)
    (htheta : theta ^ 2 ≤ 1)
    (hgrowth : nu * N ^ 2 ≤ c * A) :
    cStar ^ 3 ≤ K * r ^ 2 * epsilon ^ 2 * nu * A := by
  have hquad := active_return_gives_quadratic_ceiling
    cStar c r V epsilon nu N theta
    (le_of_lt hcStar) hr hepsilon hnu hN hcoeffLow hactive hreturn htheta
  exact cubic_coefficient_ceiling
    cStar c K r epsilon nu N A hcStar hK hr hepsilon hnu hN hA
    hquad hgrowth hcoeffHigh

/-- CRITIC: once the target coefficient exceeds the cubic ceiling, no hidden
choice of packet volume, angle, high frequency, or actual coefficient can
satisfy all uncancelled-route gates. -/
theorem no_uncancelled_route_above_cubic_ceiling
    (cStar K r epsilon nu A : ℝ)
    (hcStar : 0 < cStar)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hepsilon : 0 ≤ epsilon)
    (hnu : 0 ≤ nu) (hA : 0 ≤ A)
    (hexcess : K * r ^ 2 * epsilon ^ 2 * nu * A < cStar ^ 3) :
    ¬ ∃ c V N theta : ℝ,
      0 ≤ N ∧
      cStar ≤ c ∧ c ≤ K * cStar ∧
      c ^ 2 ≤ r ^ 2 * V ∧
      r * V ≤ epsilon * nu * N * theta ^ 2 ∧
      theta ^ 2 ≤ 1 ∧
      nu * N ^ 2 ≤ c * A := by
  rintro ⟨c, V, N, theta, hN, hcoeffLow, hcoeffHigh,
    hactive, hreturn, htheta, hgrowth⟩
  have hceiling := full_uncancelled_route_cubic_ceiling
    cStar c K r V epsilon nu N theta A
    hcStar hK hr hepsilon hnu hN hA hcoeffLow hcoeffHigh
    hactive hreturn htheta hgrowth
  linarith

/-- Concrete unit-budget obstruction: target coefficient two already exceeds
what the normalized uncancelled route can support when all fixed constants
are one and `r=1`. -/
theorem unit_budget_target_two_exceeds_ceiling :
    (1 : ℝ) * 1 ^ 2 * 1 ^ 2 * 1 * 1 < 2 ^ 3 := by
  norm_num

#print axioms active_return_gives_quadratic_ceiling
#print axioms cubic_coefficient_ceiling
#print axioms full_uncancelled_route_cubic_ceiling
#print axioms no_uncancelled_route_above_cubic_ceiling
#print axioms unit_budget_target_two_exceeds_ceiling

end NSGolayVolumeViscosity
