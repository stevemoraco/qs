import Mathlib

namespace Millennium.YangMills

/-- For `n ≥ 2`, the number of incidences is at most twice the number of
non-root incidences. -/
theorem incidence_le_twice_nonroot (n : ℕ) (hn : 2 ≤ n) :
    n ≤ 2 * (n - 1) := by
  omega

/-- A fixed exponential incidence charge is paid by a linear-in-incidence
support reserve once the pivot separation is sufficiently large. -/
theorem pivot_incidence_charge_absorbed
    (lambda mu cp R : ℝ) (n : ℕ)
    (hn : 2 ≤ n)
    (hlambda : 0 ≤ lambda)
    (hscale : 2 * lambda ≤ mu * cp * R) :
    lambda * (n : ℝ) ≤ mu * cp * R * ((n - 1 : ℕ) : ℝ) := by
  have hnNat : n ≤ 2 * (n - 1) := incidence_le_twice_nonroot n hn
  have hnReal : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnNat
  have hnonroot : 0 ≤ ((n - 1 : ℕ) : ℝ) := by positivity
  calc
    lambda * (n : ℝ) ≤ lambda * (2 * ((n - 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hnReal hlambda
    _ = (2 * lambda) * ((n - 1 : ℕ) : ℝ) := by ring
    _ ≤ (mu * cp * R) * ((n - 1 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_right hscale hnonroot

/-- If the actual paid support cost dominates the geometric lower bound, then
the same separation condition absorbs the incidence charge into that cost. -/
theorem pivot_incidence_charge_absorbed_by_support
    (lambda mu cp R cost : ℝ) (n : ℕ)
    (hn : 2 ≤ n)
    (hlambda : 0 ≤ lambda)
    (hmu : 0 ≤ mu)
    (hscale : 2 * lambda ≤ mu * cp * R)
    (hcost : cp * R * ((n - 1 : ℕ) : ℝ) ≤ cost) :
    lambda * (n : ℝ) ≤ mu * cost := by
  have hbase := pivot_incidence_charge_absorbed lambda mu cp R n hn hlambda hscale
  have hcost' : mu * (cp * R * ((n - 1 : ℕ) : ℝ)) ≤ mu * cost := by
    exact mul_le_mul_of_nonneg_left hcost hmu
  calc
    lambda * (n : ℝ) ≤ mu * cp * R * ((n - 1 : ℕ) : ℝ) := hbase
    _ = mu * (cp * R * ((n - 1 : ℕ) : ℝ)) := by ring
    _ ≤ mu * cost := hcost'

/-- If the exponent paid by one atom dominates its incidence charge, charging
that atom cannot increase its nonnegative base mass. -/
theorem charged_atom_le_base
    (lambda mu cost base : ℝ) (n : ℕ)
    (hbase : 0 ≤ base)
    (hpay : lambda * (n : ℝ) ≤ mu * cost) :
    Real.exp (lambda * (n : ℝ)) * (Real.exp (-mu * cost) * base) ≤ base := by
  have hsum : lambda * (n : ℝ) + (-mu * cost) ≤ 0 := by
    linarith
  have hexp : Real.exp (lambda * (n : ℝ) + (-mu * cost)) ≤ 1 := by
    have h := Real.exp_le_exp.mpr hsum
    simpa using h
  calc
    Real.exp (lambda * (n : ℝ)) * (Real.exp (-mu * cost) * base)
        = Real.exp (lambda * (n : ℝ) + (-mu * cost)) * base := by
            rw [Real.exp_add]
            ring
    _ ≤ 1 * base := by
      exact mul_le_mul_of_nonneg_right hexp hbase
    _ = base := by ring

/-- A finite pre-collect atomic row remains bounded after every atom is charged,
provided the charge is paid atomwise before any regrouping/collection. -/
theorem precollect_charged_row_le_unpaid
    {ι : Type*}
    (s : Finset ι)
    (lambda mu : ℝ)
    (n : ι → ℕ)
    (cost base : ι → ℝ)
    (hbase : ∀ i ∈ s, 0 ≤ base i)
    (hpay : ∀ i ∈ s, lambda * (n i : ℝ) ≤ mu * cost i) :
    (∑ i in s,
      Real.exp (lambda * (n i : ℝ)) *
        (Real.exp (-mu * cost i) * base i))
      ≤ ∑ i in s, base i := by
  exact Finset.sum_le_sum fun i hi =>
    charged_atom_le_base lambda mu (cost i) (base i) (n i)
      (hbase i hi) (hpay i hi)

/-- Source-facing version: if every atom in a finite multipivot family carries
at least the linear separated-pivot support cost used in the existing
pivot-incidence theorem, the full charged row is dominated by the original
atomic row. -/
theorem precollect_multipivot_row_paid_by_support
    {ι : Type*}
    (s : Finset ι)
    (lambda mu cp R : ℝ)
    (n : ι → ℕ)
    (cost base : ι → ℝ)
    (hn : ∀ i ∈ s, 2 ≤ n i)
    (hbase : ∀ i ∈ s, 0 ≤ base i)
    (hlambda : 0 ≤ lambda)
    (hmu : 0 ≤ mu)
    (hscale : 2 * lambda ≤ mu * cp * R)
    (hcost : ∀ i ∈ s,
      cp * R * (((n i - 1 : ℕ) : ℝ)) ≤ cost i) :
    (∑ i in s,
      Real.exp (lambda * (n i : ℝ)) *
        (Real.exp (-mu * cost i) * base i))
      ≤ ∑ i in s, base i := by
  apply precollect_charged_row_le_unpaid s lambda mu n cost base hbase
  intro i hi
  exact pivot_incidence_charge_absorbed_by_support
    lambda mu cp R (cost i) (n i)
    (hn i hi) hlambda hmu hscale (hcost i hi)

#print axioms precollect_charged_row_le_unpaid
#print axioms precollect_multipivot_row_paid_by_support

end Millennium.YangMills
