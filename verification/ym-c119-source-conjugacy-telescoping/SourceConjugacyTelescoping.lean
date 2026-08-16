import Mathlib

/-!
# Scale-local source conjugacy telescoping

Finite scalar model of the corrected Part-V to Section-8 handoff target.
If a normalized step is obtained by conjugating an underlying transport by
scale-dependent coordinate changes, adjacent coordinate factors cancel in a
product.  Hence one does not multiply an independent norm-equivalence cost at
every scale; only endpoint coordinate costs remain, conditional on a genuine
scale-local conjugacy theorem.

This file does not formalize Kirk's Banach spaces, source-renormalization
matrices, RG maps, Schwinger functions, OS reconstruction, Yang--Mills, a mass
gap, or a Clay theorem.
-/

namespace Millennium.YangMills.SourceConjugacyTelescoping

noncomputable def normalizedStep (cNext t c x : ℝ) : ℝ :=
  cNext * (t * (x / c))

theorem two_step_conjugacy_cancels
    (c0 c1 c2 t0 t1 x : ℝ)
    (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0) :
    normalizedStep c2 t1 c1 (normalizedStep c1 t0 c0 x) =
      c2 * ((t1 * t0) * (x / c0)) := by
  dsimp [normalizedStep]
  field_simp [hc0, hc1] <;> ring

theorem two_step_multiplier_identity
    (c0 c1 c2 t0 t1 : ℝ)
    (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0) :
    (c2 * t1 / c1) * (c1 * t0 / c0) =
      c2 * (t1 * t0) / c0 := by
  field_simp [hc0, hc1]

theorem endpoint_cost_bounds_two_step_product
    (c0 c1 c2 t0 t1 B C0 C2 : ℝ)
    (hc0 : 0 < c0)
    (hc1 : c1 ≠ 0)
    (hc2 : 0 ≤ c2)
    (hprod : |t1 * t0| ≤ B)
    (hleft : c2 ≤ C2)
    (hright : 1 / c0 ≤ C0)
    (hB : 0 ≤ B) :
    |(c2 * t1 / c1) * (c1 * t0 / c0)| ≤ C2 * B * C0 := by
  rw [two_step_multiplier_identity c0 c1 c2 t0 t1 (ne_of_gt hc0) hc1]
  have hc0nonneg : 0 ≤ 1 / c0 := by positivity
  have hc2nonneg : 0 ≤ c2 := hc2
  have hC2 : 0 ≤ C2 := le_trans hc2nonneg hleft
  have hC0 : 0 ≤ C0 := le_trans hc0nonneg hright
  rw [abs_div, abs_mul]
  rw [abs_of_nonneg hc2nonneg, abs_of_pos hc0]
  have h1 : c2 * |t1 * t0| ≤ C2 * B := by
    exact mul_le_mul hleft hprod (abs_nonneg _) hC2
  have h2 : c2 * |t1 * t0| * (1 / c0) ≤ C2 * B * C0 :=
    mul_le_mul h1 hright hc0nonneg (mul_nonneg hC2 hB)
  simpa [div_eq_mul_inv, mul_assoc] using h2

#print axioms two_step_conjugacy_cancels
#print axioms two_step_multiplier_identity
#print axioms endpoint_cost_bounds_two_step_product

end Millennium.YangMills.SourceConjugacyTelescoping
