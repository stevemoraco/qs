import Mathlib

/-!
# `O(u^2)` scheme comparison: reciprocal and ratio window

Finite scalar bridge for the Yang--Mills dimensional-transmutation denominator.

If two positive weak coupling coordinates satisfy

    |v - u| <= C * u^2

and the weak point is small enough that `C*u <= 1/2`, then `v` remains within
one factor of `u`, the reciprocal displacement is uniformly bounded by `2*C`,
and the ratio `v/u` lies in `[1/2, 3/2]`.

These are exactly the non-asymptotic finite inequalities used before applying
a correctly typed Yang--Mills RG/Lambda scheme theorem.  They do not construct
a renormalized coupling, beta function, Lambda parameter, OS theory, or mass
gap.
-/

namespace Millennium.YangMills

/-- A local quadratic scheme error keeps the transformed weak coupling between
one half and three halves of the reference coupling. -/
theorem o2_scheme_local_window
    {u v C : ℝ}
    (hu : 0 < u)
    (hC : 0 ≤ C)
    (hsmall : C * u ≤ 1 / 2)
    (herr : |v - u| ≤ C * u ^ 2) :
    u / 2 ≤ v ∧ v ≤ 3 * u / 2 := by
  have hquad : C * u ^ 2 ≤ u / 2 := by
    nlinarith
  have habs : -(C * u ^ 2) ≤ v - u ∧ v - u ≤ C * u ^ 2 :=
    abs_le.mp herr
  constructor <;> nlinarith

/-- The same hypotheses give a fixed dimensionless ratio window. -/
theorem o2_scheme_ratio_window
    {u v C : ℝ}
    (hu : 0 < u)
    (hC : 0 ≤ C)
    (hsmall : C * u ≤ 1 / 2)
    (herr : |v - u| ≤ C * u ^ 2) :
    (1 : ℝ) / 2 ≤ v / u ∧ v / u ≤ 3 / 2 := by
  have hwin := o2_scheme_local_window hu hC hsmall herr
  constructor
  · exact (le_div_iff₀ hu).2 (by nlinarith [hwin.1])
  · exact (div_le_iff₀ hu).2 (by nlinarith [hwin.2])

/-- Once `v >= u/2`, the quadratic coordinate error is bounded by the
cross-multiplied denominator needed for reciprocal control. -/
theorem o2_scheme_cross_bound
    {u v C : ℝ}
    (hu : 0 < u)
    (hC : 0 ≤ C)
    (hv : u / 2 ≤ v)
    (herr : |v - u| ≤ C * u ^ 2) :
    |u - v| ≤ 2 * C * (u * v) := by
  have hswap : |u - v| = |v - u| := abs_sub_comm u v
  rw [hswap]
  have hquad : C * u ^ 2 ≤ 2 * C * (u * v) := by
    nlinarith
  exact le_trans herr hquad

/-- A uniform `O(u^2)` finite scheme error produces a uniform reciprocal
shift bound.  This is the finite algebra behind the fact that the leading
exponential in an asymptotically-free Lambda factor cannot acquire an
unbounded regulator-dependent multiplicative drift. -/
theorem o2_scheme_reciprocal_bound
    {u v C : ℝ}
    (hu : 0 < u)
    (hC : 0 ≤ C)
    (hsmall : C * u ≤ 1 / 2)
    (herr : |v - u| ≤ C * u ^ 2) :
    |1 / v - 1 / u| ≤ 2 * C := by
  have hwin := o2_scheme_local_window hu hC hsmall herr
  have hv : 0 < v := by linarith [hwin.1]
  have hcross := o2_scheme_cross_bound hu hC hwin.1 herr
  have huv : 0 < u * v := mul_pos hu hv
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hv0 : v ≠ 0 := ne_of_gt hv
  have hid : 1 / v - 1 / u = (u - v) / (u * v) := by
    field_simp [hu0, hv0]
  rw [hid, abs_div, abs_of_pos huv]
  exact (div_le_iff₀ huv).2 hcross

#print axioms o2_scheme_local_window
#print axioms o2_scheme_ratio_window
#print axioms o2_scheme_cross_bound
#print axioms o2_scheme_reciprocal_bound

end Millennium.YangMills
