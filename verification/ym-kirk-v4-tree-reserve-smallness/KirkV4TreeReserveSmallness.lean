import Mathlib

namespace Millennium.YangMills

/-!
# Tree-reserve incidence payment with explicit separation smallness

Finite arithmetic bridge for the repaired Kirk-v4 HT5 reference row.  A
permanent tree/support exponent can be split three ways: a weaker retained
spatial exponent, the per-pivot incidence charge, and one explicit positive
`R`-dependent reserve.  This is the scalar fact needed to recover a row that
actually tends to zero as pivot separation grows.

No Yang--Mills support estimate, compact collect, polymer theorem, continuum
limit, Osterwalder--Schrader reconstruction, spectral gap, or Clay conclusion
is proved here.
-/

/-- For `n >= 2`, the incidence count is at most twice the number of non-root
incidences. -/
theorem incidence_le_twice_nonroot_smallness (n : ℕ) (hn : 2 ≤ n) :
    n ≤ 2 * (n - 1) := by
  omega

/-- A tree reserve can pay the pivot charge, retain a weaker diameter exponent,
and still leave one explicit separation factor.  The stronger scale condition
`4 * lambda <= (aTree - mDiam) * cp * R` spends at most half of the unused
support exponent on the incidence charge; the other half pays a positive
`R`-dependent smallness reserve. -/
theorem tree_reserve_pays_incidence_diameter_and_R_smallness
    (lambda aTree mDiam cp R treeCost diamCost : ℝ) (n : ℕ)
    (hn : 2 ≤ n)
    (hlambda : 0 ≤ lambda)
    (hgap : 0 ≤ aTree - mDiam)
    (hmDiam : 0 ≤ mDiam)
    (hcpR : 0 ≤ cp * R)
    (hscale : 4 * lambda ≤ (aTree - mDiam) * cp * R)
    (hgeom : cp * R * ((n - 1 : ℕ) : ℝ) ≤ treeCost)
    (hdiam : diamCost ≤ treeCost) :
    lambda * (n : ℝ) + mDiam * diamCost +
        ((aTree - mDiam) / 2) * (cp * R) ≤
      aTree * treeCost := by
  have hnNat : n ≤ 2 * (n - 1) :=
    incidence_le_twice_nonroot_smallness n hn
  have hnReal : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnNat
  have hnonrootNat : 1 ≤ n - 1 := by omega
  have hnonrootReal : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnonrootNat
  have hhalfGap : 0 ≤ (aTree - mDiam) / 2 := by
    linarith
  have hscaleHalf :
      2 * lambda ≤ ((aTree - mDiam) / 2) * cp * R := by
    nlinarith [hscale]
  have hchargeGeom :
      lambda * (n : ℝ) ≤
        ((aTree - mDiam) / 2) * cp * R * ((n - 1 : ℕ) : ℝ) := by
    have hnonroot : 0 ≤ ((n - 1 : ℕ) : ℝ) := by positivity
    calc
      lambda * (n : ℝ) ≤ lambda * (2 * ((n - 1 : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hnReal hlambda
      _ = (2 * lambda) * ((n - 1 : ℕ) : ℝ) := by ring
      _ ≤ (((aTree - mDiam) / 2) * cp * R) *
          ((n - 1 : ℕ) : ℝ) := by
        exact mul_le_mul_of_nonneg_right hscaleHalf hnonroot
  have hchargeTree :
      lambda * (n : ℝ) ≤ ((aTree - mDiam) / 2) * treeCost := by
    have htree :
        ((aTree - mDiam) / 2) *
            (cp * R * ((n - 1 : ℕ) : ℝ)) ≤
          ((aTree - mDiam) / 2) * treeCost := by
      exact mul_le_mul_of_nonneg_left hgeom hhalfGap
    calc
      lambda * (n : ℝ) ≤
          ((aTree - mDiam) / 2) * cp * R *
            ((n - 1 : ℕ) : ℝ) := hchargeGeom
      _ = ((aTree - mDiam) / 2) *
          (cp * R * ((n - 1 : ℕ) : ℝ)) := by ring
      _ ≤ ((aTree - mDiam) / 2) * treeCost := htree
  have hcpGeom :
      cp * R ≤ cp * R * ((n - 1 : ℕ) : ℝ) := by
    calc
      cp * R = (cp * R) * 1 := by ring
      _ ≤ (cp * R) * ((n - 1 : ℕ) : ℝ) := by
        exact mul_le_mul_of_nonneg_left hnonrootReal hcpR
  have hcpTree : cp * R ≤ treeCost := le_trans hcpGeom hgeom
  have hsmallTree :
      ((aTree - mDiam) / 2) * (cp * R) ≤
        ((aTree - mDiam) / 2) * treeCost := by
    exact mul_le_mul_of_nonneg_left hcpTree hhalfGap
  have hdiamPaid : mDiam * diamCost ≤ mDiam * treeCost := by
    exact mul_le_mul_of_nonneg_left hdiam hmDiam
  calc
    lambda * (n : ℝ) + mDiam * diamCost +
          ((aTree - mDiam) / 2) * (cp * R)
        ≤ ((aTree - mDiam) / 2) * treeCost +
          mDiam * treeCost +
          ((aTree - mDiam) / 2) * treeCost := by
            exact add_le_add (add_le_add hchargeTree hdiamPaid) hsmallTree
    _ = aTree * treeCost := by ring

/-- Exponential form: after paying incidence and the retained diameter weight,
there remains the explicit factor `exp(-((aTree-mDiam)/2)*cp*R)`. -/
theorem exp_incidence_diameter_with_R_smallness_le_tree_reserve
    (lambda aTree mDiam cp R treeCost diamCost : ℝ) (n : ℕ)
    (hn : 2 ≤ n)
    (hlambda : 0 ≤ lambda)
    (hgap : 0 ≤ aTree - mDiam)
    (hmDiam : 0 ≤ mDiam)
    (hcpR : 0 ≤ cp * R)
    (hscale : 4 * lambda ≤ (aTree - mDiam) * cp * R)
    (hgeom : cp * R * ((n - 1 : ℕ) : ℝ) ≤ treeCost)
    (hdiam : diamCost ≤ treeCost) :
    Real.exp (lambda * (n : ℝ) + mDiam * diamCost) ≤
      Real.exp (aTree * treeCost) *
        Real.exp (-((aTree - mDiam) / 2) * (cp * R)) := by
  have h := tree_reserve_pays_incidence_diameter_and_R_smallness
    lambda aTree mDiam cp R treeCost diamCost n hn hlambda hgap hmDiam
    hcpR hscale hgeom hdiam
  have hshift :
      lambda * (n : ℝ) + mDiam * diamCost ≤
        aTree * treeCost - ((aTree - mDiam) / 2) * (cp * R) := by
    linarith
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by
    convert hshift using 1 <;> ring)

#print axioms incidence_le_twice_nonroot_smallness
#print axioms tree_reserve_pays_incidence_diameter_and_R_smallness
#print axioms exp_incidence_diameter_with_R_smallness_le_tree_reserve

end Millennium.YangMills
