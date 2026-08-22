import Mathlib

/-!
# RH B140 weak-Mertens-tail finite core

Finite real/Finset algebra only.

The human analytic reduction in `stevemoraco/RH` replaces B139's selected
negative first moment by a weighted weak-L1 exceptional-set envelope.  The
load-bearing deterministic facts are:

* threshold mass is dominated by the selected first moment;
* one geometric threshold controls every intermediate threshold up to the
  multiplicative mesh ratio;
* one geometric bucket contributes at most its upper endpoint times its total
  weight;
* a single bottom-threshold query can underestimate hidden depth by an arbitrary
  multiplicative factor.

No primes, Mertens theorem, Zhao theorem, Stadlmann gap estimate, matrix spectral
theory, zeta function, or Riemann hypothesis is formalized here.
-/

open Finset
open scoped BigOperators

namespace RHB140WeakMertensTailFinite

/-- If every selected depth is at least `lambda`, then threshold times selected
weight is bounded by the selected first moment. -/
theorem threshold_mass_le_first_moment
    {ι : Type*} (s : Finset ι) (w d : ι → ℝ) (lambda : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hd : ∀ i ∈ s, lambda ≤ d i) :
    lambda * (∑ i ∈ s, w i) ≤ ∑ i ∈ s, w i * d i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    lambda * w i = w i * lambda := by ring
    _ ≤ w i * d i := mul_le_mul_of_nonneg_left (hd i hi) (hw i hi)

/-- Monotonicity plus a multiplicative grid bracket transfers an intermediate
weak-tail product to the lower sampled threshold with loss `rho`. -/
theorem geometric_threshold_transfer
    (G : ℝ → ℝ) (rho lambda t : ℝ)
    (hrho : 0 ≤ rho) (hlambda : 0 ≤ lambda)
    (hmono : ∀ a b : ℝ, a ≤ b → G b ≤ G a)
    (hGt : 0 ≤ G t)
    (hlow : lambda ≤ t)
    (hhigh : t ≤ rho * lambda) :
    t * G t ≤ rho * lambda * G lambda := by
  have h1 : t * G t ≤ (rho * lambda) * G t :=
    mul_le_mul_of_nonneg_right hhigh hGt
  have h2 : G t ≤ G lambda := hmono lambda t hlow
  have hrl : 0 ≤ rho * lambda := mul_nonneg hrho hlambda
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hrl)

/-- A bucket whose depths are all below `rho*lambda` has first moment at most
`rho*lambda` times its total weight. -/
theorem bucket_first_moment_le_upper_endpoint
    {ι : Type*} (s : Finset ι) (w d : ι → ℝ)
    (rho lambda : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hd : ∀ i ∈ s, d i ≤ rho * lambda) :
    (∑ i ∈ s, w i * d i) ≤ (rho * lambda) * (∑ i ∈ s, w i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    w i * d i ≤ w i * (rho * lambda) :=
      mul_le_mul_of_nonneg_left (hd i hi) (hw i hi)
    _ = (rho * lambda) * w i := by ring

/-- Exact one-step hidden-depth amplification: if a true depth is `R` times the
sampled threshold, then its mass is exactly `R` times the bottom-query mass.
This is the scalar core of the fixed-shift blindness counterexample. -/
theorem hidden_depth_amplifies_bottom_query
    (N tau R : ℝ) :
    (R * tau) * N = R * (tau * N) := by
  ring

/-- If `R>1` and the bottom query has positive mass, then the hidden-depth mass
is strictly larger than the bottom-query mass. -/
theorem one_shift_can_miss_depth
    (N tau R : ℝ)
    (hN : 0 < N) (htau : 0 < tau) (hR : 1 < R) :
    tau * N < (R * tau) * N := by
  have hbase : 0 < tau * N := mul_pos htau hN
  calc
    tau * N < R * (tau * N) := by
      exact (lt_mul_iff_one_lt_left hbase).2 hR
    _ = (R * tau) * N := by ring

#print axioms threshold_mass_le_first_moment
#print axioms geometric_threshold_transfer
#print axioms bucket_first_moment_le_upper_endpoint
#print axioms hidden_depth_amplifies_bottom_query
#print axioms one_shift_can_miss_depth

end RHB140WeakMertensTailFinite
