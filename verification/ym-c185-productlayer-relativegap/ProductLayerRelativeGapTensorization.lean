import Mathlib

/-!
# Product-layer relative-gap tensorization core

Finite scalar shadows of a volume-uniform Markov/OS repair.

If one local positive contraction `Q` retains a fraction `c` of the Dirichlet
form of an ideal contraction `P`, then `Q <= (1-c)I + cP`.  On disjoint tensor
factors, the comparison does not need to pay a factor `c` per spatial block.
The load-bearing scalar inequality is

  Π ((1-c) + c p_i) <= (1-c) + c Π p_i

for `p_i in [0,1]`.

A second exact identity records that a common positive OS multiplication
sandwich does not worsen the same retained gap fraction:

  I - M Q M = (I-M^2) + M(I-Q)M.

The operator tensorization and noncommutative sandwich theorem use positivity,
Loewner order, and spectral calculus and remain human/source theorems outside
this finite scalar file.

No lattice gauge theory, transfer operator source identification, interacting
polymer estimate, Osterwalder--Schrader reconstruction, Yang--Mills mass gap,
or Clay theorem is formalized here.
-/

namespace Millennium.YangMills.ProductLayerRelativeGapTensorization

/-- The Bernoulli-mixture map `p ↦ (1-c)+c p` is supermultiplicative on
`[0,1]`.  Equivalently, a common retained gap fraction does not square when two
independent factors are tensored. -/
theorem mixture_product_le_mixture_product
    (c p r : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hp1 : p ≤ 1)
    (hr1 : r ≤ 1) :
    ((1 - c) + c * p) * ((1 - c) + c * r)
      ≤ (1 - c) + c * (p * r) := by
  have hnonneg : 0 ≤ c * (1 - c) * (1 - p) * (1 - r) := by
    positivity
  nlinarith

/-- Binary scalar tensorization: if each actual factor is bounded by the
mixture `(1-c) + c*p`, then the product actual factor is bounded by the same
mixture applied to the ideal product, with the *same* `c`. -/
theorem binary_product_tensorization
    (c p r q s : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr1 : r ≤ 1)
    (hs0 : 0 ≤ s)
    (hq : q ≤ (1 - c) + c * p)
    (hs : s ≤ (1 - c) + c * r) :
    q * s ≤ (1 - c) + c * (p * r) := by
  have hb0 : 0 ≤ (1 - c) + c * p := by positivity
  have hprod : q * s ≤ ((1 - c) + c * p) * ((1 - c) + c * r) := by
    exact mul_le_mul hq hs hs0 hb0
  exact hprod.trans
    (mixture_product_le_mixture_product c p r hc0 hc1 hp1 hr1)

/-- Rewriting the previous result in spectral-gap form: the product gap retains
at least the same fraction `c` of the ideal product gap. -/
theorem binary_gap_fraction_preserved
    (c p r q s : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr1 : r ≤ 1)
    (hs0 : 0 ≤ s)
    (hq : q ≤ (1 - c) + c * p)
    (hs : s ≤ (1 - c) + c * r) :
    c * (1 - p * r) ≤ 1 - q * s := by
  have h := binary_product_tensorization c p r q s
    hc0 hc1 hp0 hp1 hr1 hs0 hq hs
  nlinarith

/-- Scalar shadow of the common OS sandwich theorem.  If `q` is no larger than
the retained-gap mixture of `p`, then multiplying both transfer factors by the
same `m^2` with `0<=m<=1` preserves the same gap fraction `c`. -/
theorem common_sandwich_preserves_gap_fraction
    (c m p q : ℝ)
    (hc1 : c ≤ 1)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hq : q ≤ (1 - c) + c * p) :
    c * (1 - m ^ 2 * p) ≤ 1 - m ^ 2 * q := by
  have hm2 : m ^ 2 ≤ 1 := by nlinarith [sq_nonneg m]
  have hmq : m ^ 2 * q ≤ m ^ 2 * ((1 - c) + c * p) := by
    exact mul_le_mul_of_nonneg_left hq (sq_nonneg m)
  have hnonneg : 0 ≤ (1 - c) * (1 - m ^ 2) := by positivity
  nlinarith

/-- Exact scalar decomposition behind the operator identity
`I-MQM=(I-M^2)+M(I-Q)M`. -/
theorem sandwich_gap_decomposition
    (m q : ℝ) :
    1 - m ^ 2 * q = (1 - m ^ 2) + m ^ 2 * (1 - q) := by
  ring

#print axioms mixture_product_le_mixture_product
#print axioms binary_product_tensorization
#print axioms binary_gap_fraction_preserved
#print axioms common_sandwich_preserves_gap_fraction
#print axioms sandwich_gap_decomposition

end Millennium.YangMills.ProductLayerRelativeGapTensorization
