import Mathlib

namespace Millennium.YangMills

/-!
# Kirk v4 pivot-incidence support absorption

Finite arithmetic core behind the source-level pivot-incidence geometry used in
Kirk v4 Lemma 6.30.  If a connected support carrying `n ≥ 2` selected pivots
has a paid support cost at least `cp * R * (n - 1)`, then any fixed incidence
charge `lambda * n` is absorbed once the separation `R` is large enough that
`2 * lambda ≤ mu * cp * R`, where `mu` is the unused support exponent.

This file does not prove the Yang--Mills support-geometry hypothesis itself;
it formalizes only the load-bearing scalar implication once that hypothesis is
instantiated.  No continuum, OS, spectral-gap, or Clay conclusion is encoded.
-/

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

#print axioms incidence_le_twice_nonroot
#print axioms pivot_incidence_charge_absorbed
#print axioms pivot_incidence_charge_absorbed_by_support

end Millennium.YangMills
