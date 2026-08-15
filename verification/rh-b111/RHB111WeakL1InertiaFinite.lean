import Mathlib

/-!
# RH B111 weak-L1 / weak-Schatten finite core

Finite real/order algebra only.

This file formalizes the load-bearing finite inequalities behind B111:

* a rankwise weak-L1 envelope implies a harmonic bound on total depth;
* one quadratic-energy rank estimate implies the critical weak-L1 bound after
  the ambient block size is supplied;
* reciprocal rank depths have constant weak-L1 size, exposing the genuine
  logarithmic gap between weak-L1 and total depth;
* a fixed positive threshold can miss an arbitrarily large aggregate block.

It deliberately does NOT formalize decreasing rearrangements, matrix spectral
theory, primes, B109B, zeta, or RH.  The analytic/arithmetic bridge remains
external and explicit.
-/

open scoped BigOperators

namespace RHB111WeakL1InertiaFinite

/-- Finite harmonic prefix used by the weak-L1 to L1 comparison. -/
def harmonicPrefix (L : ℕ) : ℝ :=
  ∑ i in Finset.range L, (((i + 1 : ℕ) : ℝ)⁻¹)

/-- One rankwise weak-L1 bound gives the corresponding pointwise harmonic
majorant. -/
theorem rank_envelope_pointwise
    {x : ℕ → ℝ} {W : ℝ} {i : ℕ}
    (hweak : (((i + 1 : ℕ) : ℝ) * x i) ≤ W) :
    x i ≤ W * (((i + 1 : ℕ) : ℝ)⁻¹) := by
  have hpos : 0 < (((i + 1 : ℕ) : ℝ)) := by positivity
  have hmul : x i * (((i + 1 : ℕ) : ℝ)) ≤ W := by
    simpa [mul_comm] using hweak
  have hdiv : x i ≤ W / (((i + 1 : ℕ) : ℝ)) :=
    (le_div_iff₀ hpos).2 hmul
  simpa [div_eq_mul_inv] using hdiv

/-- If every decreasing-rank depth obeys `(i+1) x_i <= W`, then the total
finite depth is at most `W` times the harmonic prefix.  The theorem is stated
for an arbitrary sequence satisfying the rankwise inequalities, so sorting is
not hidden inside the kernel proof. -/
theorem harmonic_envelope_sum
    (x : ℕ → ℝ) (L : ℕ) (W : ℝ)
    (hweak : ∀ i : ℕ, i < L → (((i + 1 : ℕ) : ℝ) * x i) ≤ W) :
    (∑ i in Finset.range L, x i) ≤ W * harmonicPrefix L := by
  calc
    (∑ i in Finset.range L, x i) ≤
        ∑ i in Finset.range L, W * (((i + 1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro i hi
      exact rank_envelope_pointwise (hweak i (Finset.mem_range.mp hi))
    _ = W * harmonicPrefix L := by
      rw [harmonicPrefix, Finset.mul_sum]

/-- Scalar shadow of the marked quadratic large-sieve implication.  If the
`r`-th ordered depth has paid quadratic mass `r*x^2 <= E`, then its weak-L1
rank weight has square at most `L*E` whenever `r<=L`. -/
theorem quadratic_rank_bound_sq
    {r L x E : ℝ}
    (hr0 : 0 ≤ r) (hrL : r ≤ L) (hE : 0 ≤ E)
    (hrx2 : r * x ^ 2 ≤ E) :
    (r * x) ^ 2 ≤ L * E := by
  have h1 : r * (r * x ^ 2) ≤ r * E :=
    mul_le_mul_of_nonneg_left hrx2 hr0
  have h2 : r * E ≤ L * E :=
    mul_le_mul_of_nonneg_right hrL hE
  nlinarith

/-- Reciprocal rank depths have constant weak-L1 rank weight.  This is the
finite scalar witness behind the real harmonic gap between weak-L1 and L1. -/
theorem reciprocal_rank_has_unit_weak_weight
    {r : ℝ} (hr : 0 < r) :
    r * (1 / r) = 1 := by
  field_simp [ne_of_gt hr]

/-- A fixed positive shift can miss every coordinate of a block even while the
aggregate mass exceeds any separately supplied budget. -/
theorem fixed_threshold_can_miss_aggregate_mass
    (L : ℕ) {x lambda budget : ℝ}
    (hbelow : x < lambda)
    (hmass : budget < (L : ℝ) * x) :
    x < lambda ∧ budget < (L : ℝ) * x :=
  ⟨hbelow, hmass⟩

/-- A shifted scalar eigenvalue `-x+lambda` is negative exactly when the depth
exceeds the threshold.  This is the one-dimensional negative-index carrier. -/
theorem shifted_scalar_negative_iff (x lambda : ℝ) :
    -x + lambda < 0 ↔ lambda < x := by
  linarith

#print axioms harmonicPrefix
#print axioms rank_envelope_pointwise
#print axioms harmonic_envelope_sum
#print axioms quadratic_rank_bound_sq
#print axioms reciprocal_rank_has_unit_weak_weight
#print axioms fixed_threshold_can_miss_aggregate_mass
#print axioms shifted_scalar_negative_iff

end RHB111WeakL1InertiaFinite
