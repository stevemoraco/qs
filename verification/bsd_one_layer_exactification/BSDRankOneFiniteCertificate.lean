import Mathlib

namespace BSDRankOneFiniteCertificate

/-- If the finite derivative valuation splits as a universal factor `a` plus
the limiting valuation, and is smaller than the total precision `a+b`, then
the limiting valuation lies below the error precision `b`. -/
theorem derivative_valuation_window
    {a b finiteVal limitingVal : ℕ}
    (hval : finiteVal = a + limitingVal)
    (hsmall : finiteVal < a + b) :
    limitingVal < b := by
  omega

/-- Removing the universal derivative shift preserves the strict precision
window. -/
theorem remove_universal_derivative_shift
    {n a b v : ℕ}
    (hn : n = a + b)
    (hv : v < n)
    (ha : a ≤ v) :
    v - a < b := by
  omega

/-- The derivative of a product is nonzero at a point when the first factor has
a simple zero there and the second factor is nonzero there. This is the scalar
core of the quadratic base-change step. -/
theorem product_derivative_nonzero_at_simple_zero
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {f0 f1 g0 g1 : R}
    (hf0 : f0 = 0)
    (hf1 : f1 ≠ 0)
    (hg0 : g0 ≠ 0) :
    f1 * g0 + f0 * g1 ≠ 0 := by
  rw [hf0]
  simpa using mul_ne_zero hf1 hg0

/-- The elementary corank squeeze underlying the older point-assisted
rank-one certificate. -/
theorem corank_one_plus_point_forces_rank_one
    {selmerCorank rank shaCorank : ℕ}
    (hexact : selmerCorank = rank + shaCorank)
    (hselmer : selmerCorank = 1)
    (hpoint : 1 ≤ rank) :
    rank = 1 ∧ shaCorank = 0 := by
  omega

/-- A rank lower bound and a Selmer upper bound meeting at one give exact rank. -/
theorem rank_squeeze_at_one
    {rank : ℕ}
    (hlower : 1 ≤ rank)
    (hupper : rank ≤ 1) :
    rank = 1 := by
  omega

/-- Corank zero is the only finite-length possibility in the numerical ledger. -/
theorem sha_corank_zero_of_rank_one_selmer_one
    {rank shaCorank : ℕ}
    (hexact : 1 = rank + shaCorank)
    (hrank : rank = 1) :
    shaCorank = 0 := by
  omega

/-- Abstract theorem chain for the point-free finite rank-one p-BSD
certificate. Every arithmetic bridge remains an explicit hypothesis. -/
theorem finite_derivative_implies_rank_one_pBSD_via_padic_GrossZagier
    {FiniteDerivative SignedSimple CharOrderOne SelmerCorankOne RootMinus
      AuxiliaryRankZeroTwist BaseChangeSimple HeegnerNonTorsion
      AnalyticRankOne RankOne ShaFinite PBSD : Prop}
    (hsigned : FiniteDerivative → SignedSimple)
    (hmain : SignedSimple → CharOrderOne)
    (hcontrol : CharOrderOne → SelmerCorankOne)
    (hparity : SelmerCorankOne → RootMinus)
    (haux : RootMinus → AuxiliaryRankZeroTwist)
    (hbasechange : SignedSimple → AuxiliaryRankZeroTwist → BaseChangeSimple)
    (hpadicGZ : BaseChangeSimple → HeegnerNonTorsion)
    (hcomplexGZ : HeegnerNonTorsion → AuxiliaryRankZeroTwist → AnalyticRankOne)
    (hGZK : AnalyticRankOne → RankOne ∧ ShaFinite)
    (hbsd : AnalyticRankOne → PBSD)
    (hfinite : FiniteDerivative) :
    SignedSimple ∧ CharOrderOne ∧ SelmerCorankOne ∧ RootMinus ∧
      AuxiliaryRankZeroTwist ∧ BaseChangeSimple ∧ HeegnerNonTorsion ∧
      AnalyticRankOne ∧ RankOne ∧ ShaFinite ∧ PBSD := by
  have hs := hsigned hfinite
  have hc := hmain hs
  have hsel := hcontrol hc
  have hr := hparity hsel
  have ha := haux hr
  have hb := hbasechange hs ha
  have hh := hpadicGZ hb
  have han := hcomplexGZ hh ha
  have hrf := hGZK han
  exact ⟨hs, hc, hsel, hr, ha, hb, hh, han, hrf.1, hrf.2, hbsd han⟩

/-- Abstract theorem chain for the older point-assisted certificate. -/
theorem finite_derivative_and_point_imply_rank_one_pBSD
    {FiniteDerivative SignedSimple CharOrderOne SelmerCorankOne
      PointNonTorsion RankOne ShaPFinite AnalyticRankOne PBSD : Prop}
    (hsigned : FiniteDerivative → SignedSimple)
    (hmain : SignedSimple → CharOrderOne)
    (hcontrol : CharOrderOne → SelmerCorankOne)
    (harith : SelmerCorankOne → PointNonTorsion → RankOne ∧ ShaPFinite)
    (hpconverse : SelmerCorankOne → ShaPFinite → AnalyticRankOne)
    (hbsd : AnalyticRankOne → PBSD)
    (hfinite : FiniteDerivative)
    (hpoint : PointNonTorsion) :
    SignedSimple ∧ CharOrderOne ∧ SelmerCorankOne ∧
      RankOne ∧ ShaPFinite ∧ AnalyticRankOne ∧ PBSD := by
  have hs := hsigned hfinite
  have hc := hmain hs
  have hsel := hcontrol hc
  have hra := harith hsel hpoint
  have han := hpconverse hsel hra.2
  exact ⟨hs, hc, hsel, hra.1, hra.2, han, hbsd han⟩

/-- A simple signed zero without either the p-adic Gross--Zagier bridge or a
point does not force algebraic rank one: this finite countermodel has Selmer
corank one, rank zero, and Sha corank one. -/
theorem simple_signed_zero_without_global_bridge_has_rank_zero_countermodel :
    ∃ selmerCorank rank shaCorank : ℕ,
      selmerCorank = 1 ∧
      selmerCorank = rank + shaCorank ∧
      rank = 0 ∧ shaCorank = 1 := by
  exact ⟨1, 0, 1, rfl, rfl, rfl, rfl⟩

#print axioms derivative_valuation_window
#print axioms remove_universal_derivative_shift
#print axioms product_derivative_nonzero_at_simple_zero
#print axioms corank_one_plus_point_forces_rank_one
#print axioms finite_derivative_implies_rank_one_pBSD_via_padic_GrossZagier
#print axioms finite_derivative_and_point_imply_rank_one_pBSD
#print axioms simple_signed_zero_without_global_bridge_has_rank_zero_countermodel

end BSDRankOneFiniteCertificate
