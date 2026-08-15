import Mathlib

/-!
# RH B133 Mertens perturbation finite core

Finite real-order algebra only.

The human B133 reduction replaces the primitive B46 Haar window by a cumulative
Mertens-type coordinate and then deletes proper prime powers by a nonnegative
critical-size remainder.  The analytic steps (von Mangoldt sums, the Mellin
transform, Landau's theorem, zeta continuation, and RH) are deliberately absent.

This file formalizes only the load-bearing finite inequalities needed to move
one-sided positive mass across an additive perturbation and the asymmetric
monotonicity available when the perturbation is nonnegative.
-/

open Finset
open scoped BigOperators

namespace RHB133MertensPerturbationFinite

/-- Positive part is 1-Lipschitz in the one-sided upper direction. -/
theorem posPart_add_le (x e : ℝ) :
    max (x + e) 0 ≤ max x 0 + |e| := by
  apply max_le
  · have hx : x ≤ max x 0 := le_max_left _ _
    have he : e ≤ |e| := le_abs_self e
    exact (add_le_add hx he).trans_eq (by ring)
  · exact add_nonneg (le_max_right _ _) (abs_nonneg e)

/-- The reverse one-sided perturbation inequality. -/
theorem posPart_le_add (x e : ℝ) :
    max x 0 ≤ max (x + e) 0 + |e| := by
  apply max_le
  · have hx : x + e ≤ max (x + e) 0 := le_max_left _ _
    have he : -e ≤ |e| := by
      have h := le_abs_self (-e)
      simpa using h
    calc
      x = (x + e) + (-e) := by ring
      _ ≤ max (x + e) 0 + |e| := add_le_add hx he
  · exact add_nonneg (le_max_right _ _) (abs_nonneg e)

/-- A nonnegative perturbation can only increase the positive part. -/
theorem posPart_mono_nonneg {x e : ℝ} (he : 0 ≤ e) :
    max x 0 ≤ max (x + e) 0 := by
  exact max_le_max (by linarith) le_rfl

/-- Weighted finite positive mass changes by at most the weighted absolute
perturbation, upper direction. -/
theorem weighted_posPart_perturbation_upper
    {ι : Type*} (s : Finset ι) (w x e : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * max (x i + e i) 0) ≤
      (∑ i ∈ s, w i * max (x i) 0) +
      (∑ i ∈ s, w i * |e i|) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hp := posPart_add_le (x i) (e i)
  calc
    w i * max (x i + e i) 0
        ≤ w i * (max (x i) 0 + |e i|) :=
          mul_le_mul_of_nonneg_left hp (hw i hi)
    _ = w i * max (x i) 0 + w i * |e i| := by ring

/-- Weighted finite positive mass changes by at most the weighted absolute
perturbation, reverse direction. -/
theorem weighted_posPart_perturbation_lower
    {ι : Type*} (s : Finset ι) (w x e : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * max (x i) 0) ≤
      (∑ i ∈ s, w i * max (x i + e i) 0) +
      (∑ i ∈ s, w i * |e i|) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hp := posPart_le_add (x i) (e i)
  calc
    w i * max (x i) 0
        ≤ w i * (max (x i + e i) 0 + |e i|) :=
          mul_le_mul_of_nonneg_left hp (hw i hi)
    _ = w i * max (x i + e i) 0 + w i * |e i| := by ring

/-- If `prime = full + tail` with a nonnegative tail, positive full depth is
pointwise dominated by positive prime depth.  This is the favorable sign in the
B133 proper-prime-power deletion. -/
theorem positive_full_le_prime
    {full prime tail : ℝ}
    (hrel : prime = full + tail) (htail : 0 ≤ tail) :
    max full 0 ≤ max prime 0 := by
  rw [hrel]
  exact posPart_mono_nonneg htail

/-- For the opposite sign, the same nonnegative tail costs at most its size. -/
theorem negative_full_le_prime_plus_tail
    {full prime tail : ℝ}
    (hrel : prime = full + tail) (htail : 0 ≤ tail) :
    max (-full) 0 ≤ max (-prime) 0 + tail := by
  have hrewrite : -full = -prime + tail := by
    rw [hrel]
    ring
  rw [hrewrite]
  have h := posPart_add_le (-prime) tail
  simpa [abs_of_nonneg htail] using h

/-- A uniform absolute perturbation budget transports a finite weighted
one-sided certificate without changing its asymptotic scale. -/
theorem finite_certificate_transfer
    {ι : Type*} (s : Finset ι) (w x e : ι → ℝ) (B E : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : (∑ i ∈ s, w i * max (x i) 0) ≤ B)
    (he : (∑ i ∈ s, w i * |e i|) ≤ E) :
    (∑ i ∈ s, w i * max (x i + e i) 0) ≤ B + E := by
  exact (weighted_posPart_perturbation_upper s w x e hw).trans
    (add_le_add hx he)

#print axioms posPart_add_le
#print axioms posPart_le_add
#print axioms posPart_mono_nonneg
#print axioms weighted_posPart_perturbation_upper
#print axioms weighted_posPart_perturbation_lower
#print axioms positive_full_le_prime
#print axioms negative_full_le_prime_plus_tail
#print axioms finite_certificate_transfer

end RHB133MertensPerturbationFinite
