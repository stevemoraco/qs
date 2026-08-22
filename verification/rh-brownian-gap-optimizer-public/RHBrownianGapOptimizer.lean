import Mathlib

/-!
# RH Brownian gap optimizer: finite algebraic core

This file formalizes the local algebra behind the explicit inverse and
prefix-capacity diagonalization in `stevemoraco/RH#143`.

It proves:

* the exact secant transport identity;
* strict one-third bounds and positivity of successive optimizer masses;
* the two-point Brownian inverse equations;
* the two-point prefix-norm identity;
* scalar and two-point complete-square formulas;
* an explicit positive-mass counterexample to automatic flux positivity.

It does **not** formalize primes, Chebyshev theta, Johnston's analytic
criterion, zeta zeros, the n-point induction, or RH.
-/

namespace RHBrownianGapOptimizer

/-- The optimal Brownian-prefix mass between two positive radii. -/
def secantWeight (u v : ℝ) : ℝ :=
  u ^ 2 * v ^ 2 / (u ^ 2 + u * v + v ^ 2)

/-- The secant denominator is positive for positive radii. -/
theorem secantDenominator_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    0 < u ^ 2 + u * v + v ^ 2 := by
  have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
  have huv : 0 < u * v := mul_pos hu hv
  have hv2 : 0 < v ^ 2 := sq_pos_of_pos hv
  nlinarith

/-- The closed secant formula exactly converts the inverse-cube coordinate
increment into the inverse-radius coordinate increment. -/
theorem secant_transport {u v : ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hden : u ^ 2 + u * v + v ^ 2 ≠ 0) :
    (1 / u ^ 3 - 1 / v ^ 3) * secantWeight u v =
      1 / u - 1 / v := by
  unfold secantWeight
  field_simp [hu, hv, hden]
  <;> ring

/-- The optimizer prefix lies strictly above one third of the left squared
radius. -/
theorem one_third_sq_lt_secant {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    u ^ 2 / 3 < secantWeight u v := by
  have hv : 0 < v := lt_trans hu huv
  have hden : 0 < u ^ 2 + u * v + v ^ 2 :=
    secantDenominator_pos hu hv
  unfold secantWeight
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 3) hden).2
  have hfactor :
      3 * (u ^ 2 * v ^ 2) -
          u ^ 2 * (u ^ 2 + u * v + v ^ 2) =
        u ^ 2 * (v - u) * (2 * v + u) := by
    ring
  have hpos : 0 < u ^ 2 * (v - u) * (2 * v + u) := by
    have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
    have hgap : 0 < v - u := sub_pos.mpr huv
    have hlast : 0 < 2 * v + u := by nlinarith
    positivity
  nlinarith

/-- The optimizer prefix lies strictly below one third of the right squared
radius. -/
theorem secant_lt_one_third_sq {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    secantWeight u v < v ^ 2 / 3 := by
  have hv : 0 < v := lt_trans hu huv
  have hden : 0 < u ^ 2 + u * v + v ^ 2 :=
    secantDenominator_pos hu hv
  unfold secantWeight
  apply (div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 3)).2
  have hfactor :
      v ^ 2 * (u ^ 2 + u * v + v ^ 2) -
          3 * (u ^ 2 * v ^ 2) =
        v ^ 2 * (v - u) * (v + 2 * u) := by
    ring
  have hpos : 0 < v ^ 2 * (v - u) * (v + 2 * u) := by
    have hv2 : 0 < v ^ 2 := sq_pos_of_pos hv
    have hgap : 0 < v - u := sub_pos.mpr huv
    have hlast : 0 < v + 2 * u := by nlinarith
    positivity
  nlinarith

/-- Consecutive secant prefixes are strictly increasing. -/
theorem secant_strictMono_adjacent {u v w : ℝ}
    (hu : 0 < u) (huv : u < v) (hvw : v < w) :
    secantWeight u v < secantWeight v w := by
  have hv : 0 < v := lt_trans hu huv
  exact lt_trans (secant_lt_one_third_sq hu huv)
    (one_third_sq_lt_secant hv hvw)

/-- Every interior optimizer mass, a difference of adjacent prefixes, is
strictly positive. -/
theorem interior_optimizer_mass_pos {u v w : ℝ}
    (hu : 0 < u) (huv : u < v) (hvw : v < w) :
    0 < secantWeight v w - secantWeight u v := by
  exact sub_pos.mpr (secant_strictMono_adjacent hu huv hvw)

/-- The terminal optimizer mass is positive. -/
theorem terminal_optimizer_mass_pos {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    0 < v ^ 2 - secantWeight u v := by
  have hv : 0 < v := lt_trans hu huv
  have hsec := secant_lt_one_third_sq hu huv
  have hv2 : 0 < v ^ 2 := sq_pos_of_pos hv
  nlinarith

/-- First coordinate of the explicit two-point inverse `K b = v`. -/
theorem two_point_inverse_first {u v : ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hden : u ^ 2 + u * v + v ^ 2 ≠ 0) :
    secantWeight u v / u ^ 3 +
        (v ^ 2 - secantWeight u v) / v ^ 3 =
      1 / u := by
  unfold secantWeight
  field_simp [hu, hv, hden]
  <;> ring

/-- Second coordinate of the explicit two-point inverse `K b = v`. -/
theorem two_point_inverse_second {u v : ℝ}
    (hv : v ≠ 0)
    (hden : u ^ 2 + u * v + v ^ 2 ≠ 0) :
    secantWeight u v / v ^ 3 +
        (v ^ 2 - secantWeight u v) / v ^ 3 =
      1 / v := by
  unfold secantWeight
  field_simp [hv, hden]
  <;> ring

/-- The two-point Brownian quadratic is diagonal in prefix coordinates. -/
theorem two_point_prefix_norm (u v c₁ c₂ : ℝ) :
    c₁ ^ 2 / u ^ 3 + 2 * c₁ * c₂ / v ^ 3 + c₂ ^ 2 / v ^ 3 =
      (1 / u ^ 3 - 1 / v ^ 3) * c₁ ^ 2 +
        (1 / v ^ 3) * (c₁ + c₂) ^ 2 := by
  ring

/-- Scalar complete-square identity for one prefix cell. -/
theorem scalar_complete_square (A dv dt : ℝ) (hdt : dt ≠ 0) :
    A * dv - dt * A ^ 2 / 2 =
      dv ^ 2 / (2 * dt) - dt * (A - dv / dt) ^ 2 / 2 := by
  field_simp [hdt]
  <;> ring

/-- The exact two-point norm-deficit identity. The inverse-cube increment is
stated nonzero explicitly because it appears as a denominator. -/
theorem two_point_norm_deficit {u v a₁ a₂ : ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hden : u ^ 2 + u * v + v ^ 2 ≠ 0)
    (hdt : 1 / u ^ 3 - 1 / v ^ 3 ≠ 0) :
    2 *
        (a₁ / u + a₂ / v -
          (a₁ ^ 2 / u ^ 3 +
            2 * a₁ * a₂ / v ^ 3 +
            a₂ ^ 2 / v ^ 3) / 2) =
      (1 / u - 1 / v) ^ 2 / (1 / u ^ 3 - 1 / v ^ 3) +
        (1 / v) ^ 2 / (1 / v ^ 3) -
        (1 / u ^ 3 - 1 / v ^ 3) *
          (a₁ - secantWeight u v) ^ 2 -
        (1 / v ^ 3) * (a₁ + a₂ - v ^ 2) ^ 2 := by
  unfold secantWeight
  field_simp [hu, hv, hden, hdt]
  <;> ring

/-- The local capacity has the advertised radius form. -/
theorem local_capacity_radius_form {u v : ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hden : u ^ 2 + u * v + v ^ 2 ≠ 0)
    (hdt : 1 / u ^ 3 - 1 / v ^ 3 ≠ 0) :
    (1 / u - 1 / v) ^ 2 / (1 / u ^ 3 - 1 / v ^ 3) =
      (v - u) * u * v / (u ^ 2 + u * v + v ^ 2) := by
  field_simp [hu, hv, hden, hdt]
  <;> ring

/-- Positive masses and a positive Brownian kernel do not force positive flux. -/
theorem automatic_flux_positivity_counterexample :
    (3 : ℝ) / 1 - (3 : ℝ) ^ 2 / (2 * 1 ^ 3) = -3 / 2 := by
  norm_num

#print axioms secantDenominator_pos
#print axioms secant_transport
#print axioms one_third_sq_lt_secant
#print axioms secant_lt_one_third_sq
#print axioms secant_strictMono_adjacent
#print axioms interior_optimizer_mass_pos
#print axioms terminal_optimizer_mass_pos
#print axioms two_point_inverse_first
#print axioms two_point_inverse_second
#print axioms two_point_prefix_norm
#print axioms scalar_complete_square
#print axioms two_point_norm_deficit
#print axioms local_capacity_radius_form
#print axioms automatic_flux_positivity_counterexample

end RHBrownianGapOptimizer
