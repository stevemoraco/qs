import Mathlib

/-!
# Exterior heat-at-birth budget

This file formalizes the finite scalar inequalities used after a Duhamel
comparison for a marked child and an exterior child driven by one nonnegative
source mass.

The analytic Duhamel step supplies bounds of the form

* `marked ≤ a * I`;
* `b * exp(-x) * I ≤ exterior`;

where `x = γ τ` is the viscous time accumulated during the activation interval.
When `x ≤ 1/2`, the heat factor is at least `1/2`, so a principal source
coefficient cannot become perturbatively small merely through viscosity.

No PDE conclusion is encoded here.
-/

namespace NSExteriorHeatAtBirth

/-- On a time interval shorter than half a viscous time, the heat factor is at
least one half. -/
theorem exp_neg_ge_half {x : ℝ} (hx : x ≤ (1 : ℝ) / 2) :
    (1 : ℝ) / 2 ≤ Real.exp (-x) := by
  have hlin : -x + 1 ≤ Real.exp (-x) := Real.add_one_le_exp (-x)
  have hhalf : (1 : ℝ) / 2 ≤ -x + 1 := by linarith
  exact le_trans hhalf hlin

/-- Division-free common-source comparison.  Here `a` is the marked source
coefficient, `b` the exterior source coefficient, `I` the nonnegative source
mass, and `q` a lower bound for the exterior heat factor. -/
theorem coherent_source_budget
    {a b I q marked exterior : ℝ}
    (ha : 0 < a)
    (hb : 0 ≤ b)
    (hI : 0 ≤ I)
    (hq : (1 : ℝ) / 2 ≤ q)
    (hmarked : marked ≤ a * I)
    (hexterior : b * q * I ≤ exterior) :
    b * marked ≤ 2 * a * exterior := by
  have hby : b * marked ≤ b * (a * I) :=
    mul_le_mul_of_nonneg_left hmarked hb
  have hmul : 0 ≤ 2 * a * b * I := by positivity
  have hqmul : (2 * a * b * I) * ((1 : ℝ) / 2) ≤
      (2 * a * b * I) * q :=
    mul_le_mul_of_nonneg_left hq hmul
  have hsource : b * (a * I) ≤ 2 * a * (b * q * I) := by
    calc
      b * (a * I) = (2 * a * b * I) * ((1 : ℝ) / 2) := by ring
      _ ≤ (2 * a * b * I) * q := hqmul
      _ = 2 * a * (b * q * I) := by ring
  have hext : 2 * a * (b * q * I) ≤ 2 * a * exterior :=
    mul_le_mul_of_nonneg_left hexterior (by positivity)
  exact le_trans hby (le_trans hsource hext)

/-- Duhamel heat specialization of `coherent_source_budget`. -/
theorem coherent_birth_survives_heat
    {a b I x marked exterior : ℝ}
    (ha : 0 < a)
    (hb : 0 ≤ b)
    (hI : 0 ≤ I)
    (hx : x ≤ (1 : ℝ) / 2)
    (hmarked : marked ≤ a * I)
    (hexterior : b * Real.exp (-x) * I ≤ exterior) :
    b * marked ≤ 2 * a * exterior := by
  exact coherent_source_budget ha hb hI (exp_neg_ge_half hx) hmarked hexterior

/-- If the exterior source coefficient is at least the marked coefficient,
then the exterior amplitude is at least half the marked amplitude. -/
theorem principal_exterior_ge_half_marked
    {a b I x marked exterior : ℝ}
    (ha : 0 < a)
    (hab : a ≤ b)
    (hI : 0 ≤ I)
    (hx : x ≤ (1 : ℝ) / 2)
    (hmarked_nonneg : 0 ≤ marked)
    (hmarked : marked ≤ a * I)
    (hexterior : b * Real.exp (-x) * I ≤ exterior) :
    marked ≤ 2 * exterior := by
  have hb : 0 ≤ b := le_trans (le_of_lt ha) hab
  have hbudget : b * marked ≤ 2 * a * exterior :=
    coherent_birth_survives_heat ha hb hI hx hmarked hexterior
  have hcoef : a * marked ≤ b * marked :=
    mul_le_mul_of_nonneg_right hab hmarked_nonneg
  have hscaled : a * marked ≤ a * (2 * exterior) := by
    calc
      a * marked ≤ b * marked := hcoef
      _ ≤ 2 * a * exterior := hbudget
      _ = a * (2 * exterior) := by ring
  exact (mul_le_mul_left ha).mp hscaled

/-- With no damping, two variables driven by the same source mass are exactly
slaved at their coefficient ratio. -/
theorem undamped_common_source_slaving
    {b d I marked exterior : ℝ}
    (hmarked : marked = b * I)
    (hexterior : exterior = d * I) :
    b * exterior = d * marked := by
  rw [hmarked, hexterior]
  ring

/-- The algebraic constant-margin form used when the heat loss is represented
as a nonnegative defect bounded by `x * exterior`. -/
theorem defect_budget_forces_principal_birth
    {a b I x marked exterior loss : ℝ}
    (ha : 0 < a)
    (hb : 0 ≤ b)
    (hI : 0 ≤ I)
    (hx0 : 0 ≤ x)
    (hx : x ≤ (1 : ℝ) / 2)
    (hmarked : marked ≤ a * I)
    (hbalance : exterior + loss = b * I)
    (hloss0 : 0 ≤ loss)
    (hloss : loss ≤ x * exterior) :
    b * marked ≤ 3 * a * exterior := by
  have hext0 : 0 ≤ exterior := by
    by_contra hextneg
    have hextlt : exterior < 0 := lt_of_not_ge hextneg
    have hxl : x * exterior ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx0 (le_of_lt hextlt)
    have : loss ≤ 0 := le_trans hloss hxl
    have hloss_eq : loss = 0 := le_antisymm this hloss0
    rw [hloss_eq, add_zero] at hbalance
    have hbi : 0 ≤ b * I := mul_nonneg hb hI
    linarith
  have hbirth : b * I ≤ (3 : ℝ) / 2 * exterior := by
    calc
      b * I = exterior + loss := hbalance.symm
      _ ≤ exterior + x * exterior := add_le_add_left hloss exterior
      _ ≤ exterior + ((1 : ℝ) / 2) * exterior := by
        gcongr
      _ = (3 : ℝ) / 2 * exterior := by ring
  have hby : b * marked ≤ b * (a * I) :=
    mul_le_mul_of_nonneg_left hmarked hb
  have hmul : b * (a * I) ≤ a * ((3 : ℝ) / 2 * exterior) := by
    have := mul_le_mul_of_nonneg_left hbirth (le_of_lt ha)
    nlinarith
  calc
    b * marked ≤ b * (a * I) := hby
    _ ≤ a * ((3 : ℝ) / 2 * exterior) := hmul
    _ ≤ 3 * a * exterior := by nlinarith

#print axioms exp_neg_ge_half
#print axioms coherent_source_budget
#print axioms coherent_birth_survives_heat
#print axioms principal_exterior_ge_half_marked
#print axioms undamped_common_source_slaving
#print axioms defect_budget_forces_principal_birth

end NSExteriorHeatAtBirth
