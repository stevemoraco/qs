import Mathlib

namespace Millennium.YangMills

/-!
# Mixed-forest two-root path payment

Finite real/finite-sum algebra for the current hostile reconstruction of Kirk
v4 Theorem 6.43.

A connected tree joining two declared roots has one unique root-to-root path.
Every object on that path contributes a nonnegative reported geometric length
and an exponential payment.  If one common effective rate is no larger than
each payment per unit reported length, and the reported path spans the root
distance up to one fixed buffer overhead, then the complete path weight decays
exponentially in the root distance.

The remaining tree branches are summed by a separate strict-admission theorem.
Fixed source marks give only finitely many promoted terms and therefore change
the prefactor, not the path exponent.  A final finite Schur-row theorem records
how pointwise decay plus one lattice-growth row produces weighted row and
column bounds after weakening the exponent.

This file formalizes only that finite algebra.  It does not formalize the BKAR
forest formula, the Kotecky--Preiss theorem, Kirk's activity inventory, the
source-specific path classification, Osterwalder--Schrader reconstruction,
Yang--Mills, a mass gap, or a Clay theorem.
-/

open scoped BigOperators

/-- General paid-path theorem.  `geom i` is the geometric length reported by
one object of the unique root path and `pay i` is the exponent already paid by
that object. -/
theorem paid_reported_path_gives_exponential_decay
    {I : Type*} [DecidableEq I]
    (path : Finset I)
    (geom pay : I → ℝ)
    (distance overhead rate : ℝ)
    (hrate : 0 ≤ rate)
    (hlocal : ∀ i ∈ path, rate * geom i ≤ pay i)
    (hspan : distance ≤ overhead + ∑ i ∈ path, geom i) :
    Real.exp (-(∑ i ∈ path, pay i)) ≤
      Real.exp (rate * overhead) * Real.exp (-rate * distance) := by
  have hsum : rate * (∑ i ∈ path, geom i) ≤ ∑ i ∈ path, pay i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact hlocal i hi
  have hdist :
      rate * distance ≤ rate * overhead + ∑ i ∈ path, pay i := by
    have hscaled :
        rate * distance ≤ rate * (overhead + ∑ i ∈ path, geom i) :=
      mul_le_mul_of_nonneg_left hspan hrate
    calc
      rate * distance ≤ rate * (overhead + ∑ i ∈ path, geom i) := hscaled
      _ = rate * overhead + rate * (∑ i ∈ path, geom i) := by ring
      _ ≤ rate * overhead + ∑ i ∈ path, pay i := by linarith
  have hexponent :
      -(∑ i ∈ path, pay i) ≤ rate * overhead - rate * distance := by
    linarith
  calc
    Real.exp (-(∑ i ∈ path, pay i)) ≤
        Real.exp (rate * overhead - rate * distance) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp (rate * overhead) * Real.exp (-rate * distance) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The same path estimate with a nonnegative branch prefactor already bounded
by the strict-admission theorem. -/
theorem admitted_branch_times_paid_path_decays
    {I : Type*} [DecidableEq I]
    (path : Finset I)
    (geom pay : I → ℝ)
    (branch branchBound distance overhead rate : ℝ)
    (hbranch : 0 ≤ branch)
    (hbranchBound : branch ≤ branchBound)
    (hboundNonneg : 0 ≤ branchBound)
    (hrate : 0 ≤ rate)
    (hlocal : ∀ i ∈ path, rate * geom i ≤ pay i)
    (hspan : distance ≤ overhead + ∑ i ∈ path, geom i) :
    branch * Real.exp (-(∑ i ∈ path, pay i)) ≤
      (branchBound * Real.exp (rate * overhead)) *
        Real.exp (-rate * distance) := by
  have hpath := paid_reported_path_gives_exponential_decay
    path geom pay distance overhead rate hrate hlocal hspan
  calc
    branch * Real.exp (-(∑ i ∈ path, pay i)) ≤
        branchBound * Real.exp (-(∑ i ∈ path, pay i)) :=
      mul_le_mul_of_nonneg_right hbranchBound (Real.exp_pos _).le
    _ ≤ branchBound *
        (Real.exp (rate * overhead) * Real.exp (-rate * distance)) :=
      mul_le_mul_of_nonneg_left hpath hboundNonneg
    _ = (branchBound * Real.exp (rate * overhead)) *
        Real.exp (-rate * distance) := by ring

/-- Concrete three-class specialization matching the source proof: optical
covariance bonds, compact/Haar activities, and all previously registered
connectors. -/
theorem three_paid_path_classes_give_decay
    (distance overhead : ℝ)
    (opticalLength compactLength reportedLength : ℝ)
    (opticalPay compactPay reportedPay : ℝ)
    (opticalGeom compactGeom reportedGeom rate : ℝ)
    (hoptLen : 0 ≤ opticalLength)
    (hcompactLen : 0 ≤ compactLength)
    (hreportedLen : 0 ≤ reportedLength)
    (hrate : 0 ≤ rate)
    (hopt : rate * opticalGeom ≤ opticalPay)
    (hcompact : rate * compactGeom ≤ compactPay)
    (hreported : rate * reportedGeom ≤ reportedPay)
    (hspan : distance ≤ overhead +
      opticalGeom * opticalLength +
      compactGeom * compactLength +
      reportedGeom * reportedLength) :
    Real.exp (-(opticalPay * opticalLength +
        compactPay * compactLength +
        reportedPay * reportedLength)) ≤
      Real.exp (rate * overhead) * Real.exp (-rate * distance) := by
  have hoptPaid := mul_le_mul_of_nonneg_right hopt hoptLen
  have hcompactPaid := mul_le_mul_of_nonneg_right hcompact hcompactLen
  have hreportedPaid := mul_le_mul_of_nonneg_right hreported hreportedLen
  have hdist :
      rate * distance ≤ rate * overhead +
        opticalPay * opticalLength +
        compactPay * compactLength +
        reportedPay * reportedLength := by
    have hscaled := mul_le_mul_of_nonneg_left hspan hrate
    nlinarith
  have hexponent :
      -(opticalPay * opticalLength +
        compactPay * compactLength +
        reportedPay * reportedLength) ≤
      rate * overhead - rate * distance := by
    linarith
  calc
    Real.exp (-(opticalPay * opticalLength +
        compactPay * compactLength +
        reportedPay * reportedLength)) ≤
      Real.exp (rate * overhead - rate * distance) :=
        Real.exp_le_exp.mpr hexponent
    _ = Real.exp (rate * overhead) * Real.exp (-rate * distance) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Finitely many promoted source/root placements only add their finite
prefactors.  They cannot change an already common spatial exponent. -/
theorem finite_promotions_preserve_common_decay
    {I : Type*} [DecidableEq I]
    (promotions : Finset I)
    (term prefactor : I → ℝ)
    (distance rate : ℝ)
    (hprefactor : ∀ i ∈ promotions, 0 ≤ prefactor i)
    (hterm : ∀ i ∈ promotions,
      |term i| ≤ prefactor i * Real.exp (-rate * distance)) :
    |∑ i ∈ promotions, term i| ≤
      (∑ i ∈ promotions, prefactor i) * Real.exp (-rate * distance) := by
  calc
    |∑ i ∈ promotions, term i| ≤ ∑ i ∈ promotions, |term i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ promotions,
        prefactor i * Real.exp (-rate * distance) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i hi
    _ = (∑ i ∈ promotions, prefactor i) *
        Real.exp (-rate * distance) := by
      rw [Finset.sum_mul]

/-- Finite weighted-Schur conversion.  The analytic/lattice input is the
single growth row for the weakened exponent. -/
theorem pointwise_decay_to_weighted_finite_row
    {J : Type*} [DecidableEq J]
    (targets : Finset J)
    (kernel distance : J → ℝ)
    (constant strongRate weakRate growth : ℝ)
    (hconstant : 0 ≤ constant)
    (hpoint : ∀ j ∈ targets,
      |kernel j| ≤ constant * Real.exp (-strongRate * distance j))
    (hgrowth :
      (∑ j ∈ targets,
        Real.exp (-(strongRate - weakRate) * distance j)) ≤ growth) :
    (∑ j ∈ targets,
      Real.exp (weakRate * distance j) * |kernel j|) ≤
        constant * growth := by
  calc
    (∑ j ∈ targets,
      Real.exp (weakRate * distance j) * |kernel j|) ≤
      ∑ j ∈ targets,
        constant * Real.exp (-(strongRate - weakRate) * distance j) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        Real.exp (weakRate * distance j) * |kernel j| ≤
          Real.exp (weakRate * distance j) *
            (constant * Real.exp (-strongRate * distance j)) :=
          mul_le_mul_of_nonneg_left (hpoint j hj) (Real.exp_pos _).le
        _ = constant *
            Real.exp (-(strongRate - weakRate) * distance j) := by
          rw [← Real.exp_add]
          ring_nf
    _ = constant *
        (∑ j ∈ targets,
          Real.exp (-(strongRate - weakRate) * distance j)) := by
      rw [Finset.mul_sum]
    _ ≤ constant * growth :=
      mul_le_mul_of_nonneg_left hgrowth hconstant

#print axioms paid_reported_path_gives_exponential_decay
#print axioms admitted_branch_times_paid_path_decays
#print axioms three_paid_path_classes_give_decay
#print axioms finite_promotions_preserve_common_decay
#print axioms pointwise_decay_to_weighted_finite_row

end Millennium.YangMills
