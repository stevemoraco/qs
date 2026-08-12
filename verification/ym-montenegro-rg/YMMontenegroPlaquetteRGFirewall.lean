import Mathlib

/-!
# Finite firewalls for one-plaquette convolution as a full RG

This file formalizes only:

* exact generation of pair interactions after averaging one shared sign link;
* nonfactorization of the resulting three-boundary density;
* two joint weights with identical one-plaquette marginals but different
  two-plaquette correlation.

The sign-link identity is a finite shadow of the SU(2) shared-link Haar
calculation in the accompanying paper note. This file does not formalize SU(2),
Haar integration, lattice gauge theory, reflection positivity, a continuum
limit, or the Clay Yang–Mills theorem.
-/

namespace YMMontenegroPlaquetteRGFirewall

/-- Exact average over one internal sign link shared by three plaquettes. -/
def sharedLinkAverage (t z₁ z₂ z₃ : ℚ) : ℚ :=
  (((1 + t * z₁) * (1 + t * z₂) * (1 + t * z₃)) +
    ((1 - t * z₁) * (1 - t * z₂) * (1 - t * z₃))) / 2

/-- CRITIC: integrating the shared link generates all three pair couplings. -/
theorem shared_link_average_generates_pair_couplings
    (t z₁ z₂ z₃ : ℚ) :
    sharedLinkAverage t z₁ z₂ z₃ =
      1 + t ^ 2 * (z₁ * z₂ + z₁ * z₃ + z₂ * z₃) := by
  unfold sharedLinkAverage
  ring

/-- The generated boundary density after the exact shared-link moment
calculation. -/
def plaquetteCoupling (t z₁ z₂ z₃ : ℚ) : ℚ :=
  1 + t ^ 2 * (z₁ * z₂ + z₁ * z₃ + z₂ * z₃)

/-- A product of three independent single-plaquette factors. -/
def factoredWeight
    (f₁ f₂ f₃ : Bool → ℚ) (x₁ x₂ x₃ : Bool) : ℚ :=
  f₁ x₁ * f₂ x₂ * f₃ x₃

/-- Every product of three one-site factors obeys this cross-ratio identity. -/
theorem factored_weight_cross_ratio
    (f₁ f₂ f₃ : Bool → ℚ) :
    factoredWeight f₁ f₂ f₃ true true true *
        factoredWeight f₁ f₂ f₃ true false false =
      factoredWeight f₁ f₂ f₃ true true false *
        factoredWeight f₁ f₂ f₃ true false true := by
  simp [factoredWeight]
  ring

/-- Exact cross-ratio defect of the generated coupling. -/
theorem plaquette_coupling_cross_ratio_defect (t : ℚ) :
    plaquetteCoupling t 1 1 1 * plaquetteCoupling t 1 (-1) (-1) -
        plaquetteCoupling t 1 1 (-1) * plaquetteCoupling t 1 (-1) 1 =
      4 * t ^ 2 * (1 - t ^ 2) := by
  unfold plaquetteCoupling
  ring

/-- Convert a Boolean boundary label to the center sign `+1` or `-1`. -/
def centerSign : Bool → ℚ
  | false => 1
  | true => -1

/-- CRITIC: for `0<t<1`, the generated three-boundary density cannot be a
product of independent one-plaquette factors. -/
theorem generated_coupling_not_single_plaquette_factorizable
    (t : ℚ) (ht₀ : 0 < t) (ht₁ : t < 1) :
    ¬ ∃ f₁ f₂ f₃ : Bool → ℚ,
      ∀ x₁ x₂ x₃ : Bool,
        factoredWeight f₁ f₂ f₃ x₁ x₂ x₃ =
          plaquetteCoupling t (centerSign x₁) (centerSign x₂) (centerSign x₃) := by
  rintro ⟨f₁, f₂, f₃, hfactor⟩
  have hcross := factored_weight_cross_ratio f₁ f₂ f₃
  have hc :
      plaquetteCoupling t (-1) (-1) (-1) *
          plaquetteCoupling t (-1) 1 1 =
        plaquetteCoupling t (-1) (-1) 1 *
          plaquetteCoupling t (-1) 1 (-1) := by
    calc
      plaquetteCoupling t (-1) (-1) (-1) *
          plaquetteCoupling t (-1) 1 1 =
        factoredWeight f₁ f₂ f₃ true true true *
          factoredWeight f₁ f₂ f₃ true false false := by
            rw [hfactor true true true, hfactor true false false]
            simp [centerSign]
      _ = factoredWeight f₁ f₂ f₃ true true false *
          factoredWeight f₁ f₂ f₃ true false true := hcross
      _ = plaquetteCoupling t (-1) (-1) 1 *
          plaquetteCoupling t (-1) 1 (-1) := by
            rw [hfactor true true false, hfactor true false true]
            simp [centerSign]
  have hdef :
      plaquetteCoupling t (-1) (-1) (-1) *
          plaquetteCoupling t (-1) 1 1 -
        plaquetteCoupling t (-1) (-1) 1 *
          plaquetteCoupling t (-1) 1 (-1) =
        4 * t ^ 2 * (1 - t ^ 2) := by
    unfold plaquetteCoupling
    ring
  have htSqPos : 0 < t ^ 2 := sq_pos_of_pos ht₀
  have htSqLt : t ^ 2 < 1 := by nlinarith
  nlinarith

/-- Uniform independent joint weight on two signs. -/
def independentWeight (_ _ : Bool) : ℚ := 1

/-- Perfectly correlated joint weight, normalized to the same total mass. -/
def correlatedWeight (x y : Bool) : ℚ :=
  if x = y then 2 else 0

/-- The two joint weights have identical first-coordinate marginals. -/
theorem same_first_marginals (x : Bool) :
    independentWeight x false + independentWeight x true =
      correlatedWeight x false + correlatedWeight x true := by
  cases x <;> norm_num [independentWeight, correlatedWeight]

/-- The two joint weights have identical second-coordinate marginals. -/
theorem same_second_marginals (y : Bool) :
    independentWeight false y + independentWeight true y =
      correlatedWeight false y + correlatedWeight true y := by
  cases y <;> norm_num [independentWeight, correlatedWeight]

/-- Sign observable used for the exact correlation witness. -/
def paritySign : Bool → ℚ
  | false => 1
  | true => -1

/-- Unnormalized two-site sign correlation of a joint weight. -/
def correlationScore (w : Bool → Bool → ℚ) : ℚ :=
  w false false * paritySign false * paritySign false +
  w false true * paritySign false * paritySign true +
  w true false * paritySign true * paritySign false +
  w true true * paritySign true * paritySign true

/-- CRITIC: identical one-site marginals do not determine a two-site local
correlation. Both weights have total mass four, but their scores are zero and
four respectively. -/
theorem same_marginals_different_correlations :
    correlationScore independentWeight = 0 ∧
      correlationScore correlatedWeight = 4 := by
  norm_num [correlationScore, independentWeight, correlatedWeight, paritySign]

#print axioms shared_link_average_generates_pair_couplings
#print axioms factored_weight_cross_ratio
#print axioms plaquette_coupling_cross_ratio_defect
#print axioms generated_coupling_not_single_plaquette_factorizable
#print axioms same_first_marginals
#print axioms same_second_marginals
#print axioms same_marginals_different_correlations

end YMMontenegroPlaquetteRGFirewall
