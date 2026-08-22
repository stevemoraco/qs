import Mathlib

/-!
# RH B141 quadratic negative-Mertens finite core

Finite real/Finset algebra only.

The human analytic reduction in `stevemoraco/RH` uses a gap-weighted quadratic
negative-depth budget.  The declarations below formalize only the load-bearing
finite mechanics:

* the one-sided decrement is dominated by negative state depth plus curvature;
* weighted Cauchy turns quadratic depth into a first-moment budget;
* the same quadratic budget is exactly the marked rank-one Loewner currency via
  ordinary finite Cauchy--Schwarz.

No primes, Mertens theorem, Zhao theorem, Stadlmann gap estimate, matrix spectral
theory, zeta function, or Riemann hypothesis is formalized here.
-/

open Finset
open scoped BigOperators

namespace RHB141QuadraticMertensFinite

theorem decrement_pos_le_depth_add_curvature
    (theta m : ℝ) (htheta : 0 ≤ theta) :
    max (theta - m) 0 ≤ max (-m) 0 + theta := by
  have hleft : theta - m ≤ max (-m) 0 + theta := by
    have hneg : -m ≤ max (-m) 0 := le_max_left _ _
    linarith
  have hzero : 0 ≤ max (-m) 0 + theta :=
    add_nonneg (le_max_right _ _) htheta
  exact max_le hleft hzero

theorem weighted_first_moment_sq_le_mass_mul_energy
    {ι : Type*} (s : Finset ι) (w d : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hd : ∀ i ∈ s, 0 ≤ d i) :
    (∑ i ∈ s, w i * d i) ^ 2 ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * d i ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (f := w)
    (g := fun i => w i * d i ^ 2)
    (r := fun i => w i * d i)
  · exact hw
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg (d i))
  · intro i hi
    have : (w i * d i) ^ 2 = w i * (w i * d i ^ 2) := by ring
    exact this.le

theorem weighted_first_moment_sq_le_budget
    {ι : Type*} (s : Finset ι) (w d : ι → ℝ)
    (M E : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hd : ∀ i ∈ s, 0 ≤ d i)
    (hM : ∑ i ∈ s, w i ≤ M)
    (hE : ∑ i ∈ s, w i * d i ^ 2 ≤ E) :
    (∑ i ∈ s, w i * d i) ^ 2 ≤ M * E := by
  have hcs := weighted_first_moment_sq_le_mass_mul_energy s w d hw hd
  have hsumw : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg (fun i hi => hw i hi)
  have henergy : 0 ≤ ∑ i ∈ s, w i * d i ^ 2 := by
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg (d i)))
  have hM0 : 0 ≤ M := hsumw.trans hM
  calc
    (∑ i ∈ s, w i * d i) ^ 2
        ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, w i * d i ^ 2) := hcs
    _ ≤ M * E := by
      exact mul_le_mul hM hE henergy hM0

theorem marked_rank_one_quadratic_form_bound
    {ι : Type*} (s : Finset ι) (v x : ι → ℝ) (B : ℝ)
    (hB : ∑ i ∈ s, v i ^ 2 ≤ B) :
    (∑ i ∈ s, v i * x i) ^ 2 ≤ B * (∑ i ∈ s, x i ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s v x
  have hx : 0 ≤ ∑ i ∈ s, x i ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  calc
    (∑ i ∈ s, v i * x i) ^ 2
        ≤ (∑ i ∈ s, v i ^ 2) * (∑ i ∈ s, x i ^ 2) := hcs
    _ ≤ B * (∑ i ∈ s, x i ^ 2) :=
      mul_le_mul_of_nonneg_right hB hx

theorem marked_norm_sq_is_quadratic_budget
    {ι : Type*} (s : Finset ι) (v w d : ι → ℝ)
    (hcoord : ∀ i ∈ s, v i ^ 2 = w i * d i ^ 2) :
    (∑ i ∈ s, v i ^ 2) = ∑ i ∈ s, w i * d i ^ 2 := by
  apply Finset.sum_congr rfl
  intro i hi
  exact hcoord i hi

#print axioms decrement_pos_le_depth_add_curvature
#print axioms weighted_first_moment_sq_le_mass_mul_energy
#print axioms weighted_first_moment_sq_le_budget
#print axioms marked_rank_one_quadratic_form_bound
#print axioms marked_norm_sq_is_quadratic_budget

end RHB141QuadraticMertensFinite
