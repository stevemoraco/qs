import Mathlib

/-!
# RH exact coth-packing finite firewalls

HONESTY BOUNDARY

This file verifies only finite scalar interfaces used by the exact Cauchy-kernel
packing upgrade for nonhomogeneous actual-cluster selectors:

* the Cauchy term is monotone in the positive real-part parameter after
  cross-multiplication;
* a smaller packing constant gives a smaller selector constant;
* a stronger lower floor implies every weaker lower floor;
* the Euclidean-slab formula defines a squared pseudohyperbolic radius in
  `[0,1)`;
* exact selector and zeta-cluster hypotheses remain distinct types.

It does not formalize the infinite shifted-lattice identity, domination of an
arbitrary separated set by a lattice, Blaschke products, confluent
interpolation, Hardy/model spaces, multiplier adjoints, zeta zeros, or RH.
-/

namespace MillenniumBraid
namespace RHExactCothPackingFinite

/-- Cross-multiplied monotonicity of
`a^2 / ((x+a)^2+d^2)` in `a` for nonnegative parameters. -/
theorem cauchy_term_cross_monotone
    (a A x d : ℝ)
    (ha : 0 ≤ a)
    (haA : a ≤ A)
    (hx : 0 ≤ x) :
    a ^ 2 * ((x + A) ^ 2 + d ^ 2) ≤
      A ^ 2 * ((x + a) ^ 2 + d ^ 2) := by
  have hA : 0 ≤ A := le_trans ha haA
  have hAa : 0 ≤ A - a := sub_nonneg.mpr haA
  have hsum :
      0 ≤ 2 * A * a * x + (A + a) * (d ^ 2 + x ^ 2) := by
    positivity
  have hfactor :
      A ^ 2 * ((x + a) ^ 2 + d ^ 2) -
          a ^ 2 * ((x + A) ^ 2 + d ^ 2) =
        (A - a) *
          (2 * A * a * x + (A + a) * (d ^ 2 + x ^ 2)) := by
    ring
  have hnonneg :
      0 ≤ A ^ 2 * ((x + a) ^ 2 + d ^ 2) -
          a ^ 2 * ((x + A) ^ 2 + d ^ 2) := by
    rw [hfactor]
    exact mul_nonneg hAa hsum
  linarith

/-- Substituting a sharper nonnegative packing bound can only reduce the
selector multiplier constant. -/
theorem sharper_packing_reduces_selector_constant
    (localConstant sharp coarse : ℝ)
    (hlocal : 0 ≤ localConstant)
    (hsharp : sharp ≤ coarse) :
    localConstant * sharp ≤ localConstant * coarse := by
  exact mul_le_mul_of_nonneg_left hsharp hlocal

/-- A proved stronger lower floor automatically implies every weaker floor. -/
theorem stronger_floor_implies_weaker_floor
    (sharpFloor coarseFloor energy quadratic : ℝ)
    (hfloor : coarseFloor ≤ sharpFloor)
    (henergy : 0 ≤ energy)
    (hsharp : sharpFloor * energy ≤ quadratic) :
    coarseFloor * energy ≤ quadratic := by
  exact le_trans (mul_le_mul_of_nonneg_right hfloor henergy) hsharp

/-- The Euclidean slab denominator dominates `4 alpha^2`. -/
theorem slab_denominator_dominates
    (alpha A R : ℝ)
    (halpha : 0 ≤ alpha)
    (halphaA : alpha ≤ A) :
    4 * alpha ^ 2 ≤ 4 * A ^ 2 + R ^ 2 := by
  have hA : 0 ≤ A := le_trans halpha halphaA
  have hdiff : 0 ≤ A - alpha := sub_nonneg.mpr halphaA
  have hsum : 0 ≤ A + alpha := add_nonneg hA halpha
  have hsquares : 0 ≤ A ^ 2 - alpha ^ 2 := by
    have hprod : 0 ≤ (A - alpha) * (A + alpha) :=
      mul_nonneg hdiff hsum
    nlinarith
  nlinarith [sq_nonneg R]

/-- The displayed Euclidean-slab formula is a valid squared radius in `[0,1)`
when the slab stays a positive distance from the half-plane boundary. -/
theorem euclidean_slab_radius_sq_mem
    (alpha A R : ℝ)
    (halpha : 0 < alpha)
    (halphaA : alpha ≤ A) :
    0 ≤ 1 - (4 * alpha ^ 2) / (4 * A ^ 2 + R ^ 2) ∧
      1 - (4 * alpha ^ 2) / (4 * A ^ 2 + R ^ 2) < 1 := by
  have halpha0 : 0 ≤ alpha := le_of_lt halpha
  have hA : 0 < A := lt_of_lt_of_le halpha halphaA
  have hden : 0 < 4 * A ^ 2 + R ^ 2 := by positivity
  have hdom : 4 * alpha ^ 2 ≤ 4 * A ^ 2 + R ^ 2 :=
    slab_denominator_dominates alpha A R halpha0 halphaA
  have hquotNonneg : 0 ≤ (4 * alpha ^ 2) / (4 * A ^ 2 + R ^ 2) := by
    positivity
  have hquotLe : (4 * alpha ^ 2) / (4 * A ^ 2 + R ^ 2) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    simpa using hdom
  have hquotPos : 0 < (4 * alpha ^ 2) / (4 * A ^ 2 + R ^ 2) := by
    positivity
  constructor <;> linarith

/-- Type firewall: a uniform abstract selector geometry is not itself a proved
zeta-zero cluster decomposition. -/
inductive GeometryInput where
  | abstractSelectorGeometry
  | zetaClusterDecomposition
  deriving DecidableEq

theorem abstract_geometry_ne_zeta_decomposition :
    GeometryInput.abstractSelectorGeometry ≠
      GeometryInput.zetaClusterDecomposition := by
  decide

/-- A theorem proved under the abstract geometry stays there until a separate
zeta-specific partition theorem is supplied. -/
theorem abstract_selector_stays_abstract
    (P : GeometryInput → Prop)
    (h : P GeometryInput.abstractSelectorGeometry) :
    P GeometryInput.abstractSelectorGeometry := h

#print axioms cauchy_term_cross_monotone
#print axioms sharper_packing_reduces_selector_constant
#print axioms stronger_floor_implies_weaker_floor
#print axioms slab_denominator_dominates
#print axioms euclidean_slab_radius_sq_mem
#print axioms abstract_geometry_ne_zeta_decomposition
#print axioms abstract_selector_stays_abstract

end RHExactCothPackingFinite
end MillenniumBraid
