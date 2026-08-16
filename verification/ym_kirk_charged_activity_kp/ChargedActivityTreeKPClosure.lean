import Mathlib

namespace Millennium.YangMills

/-!
# Charged activity rows close the connected-family tree budget

Finite real/combinatorial majorant for the complex compact-denominator repair.

The source-level application has a finite pivot set, a finite activity family,
nonnegative activity majorants, and one arbitrary incidence charge.  A rooted
connected-family exploration has the vector recursion

`T_{m+1}(p) <= sum_{A contains p} w(A) * exp(sum_{q in supp(A)} T_m(q))`.

If the activity row with charge `exp(c * |supp(A)|)` is at most `eps`, and
`eps <= c`, then every finite tree depth remains at most `eps` at every pivot.
Thus an arbitrarily small charged activity row supplies the per-pivot polymer
row needed by the Kotecky--Preiss admission step, once the separate spanning-
tree/first-incidence majorization is instantiated.

This file formalizes only the finite exponential-charge and recursion algebra.
It does not formalize Kirk's activity estimates, the connected-family spanning-
tree majorization, the Kotecky--Preiss theorem, Theorem 6.43, OS reconstruction,
Yang--Mills, a mass gap, or a Clay theorem.
-/

open scoped BigOperators

/-- A nonnegative support-size exponent is monotone when the union cardinality
is replaced by any larger total incidence count. -/
theorem union_support_charge_le_total_incidence_charge
    (alpha beta : ℝ) (u total : ℕ)
    (hcoeff : 0 ≤ alpha + beta)
    (hu : u ≤ total) :
    Real.exp ((u : ℝ) * (alpha + beta)) ≤
      Real.exp ((total : ℝ) * (alpha + beta)) := by
  apply Real.exp_le_exp.mpr
  have hcast : (u : ℝ) ≤ (total : ℝ) := by
    exact_mod_cast hu
  exact mul_le_mul_of_nonneg_right hcast hcoeff

/-- The total incidence charge splits exactly into the support/reference/KP
charge and the spare tree-branch charge. -/
theorem incidence_charge_exact_split
    (alpha beta c : ℝ) (n : ℕ) :
    Real.exp ((n : ℝ) * (alpha + beta + c)) =
      Real.exp ((n : ℝ) * (alpha + beta)) *
        Real.exp ((n : ℝ) * c) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- A uniformly charged activity row bounds every finite-depth vector tree
recursion.

The recurrence is deliberately an inequality: any concrete first-incidence or
spanning-tree exploration may overcount its connected families and still use
this theorem.  The support-subset hypothesis is the finite firewall preventing
a branch from escaping the pivot universe on which the induction is known. -/
theorem charged_activity_row_closes_vector_tree_recursion
    {A P : Type*} [DecidableEq A] [DecidableEq P]
    (activities : Finset A)
    (pivots : Finset P)
    (support : A → Finset P)
    (weight : A → ℝ)
    (T : ℕ → P → ℝ)
    (c eps : ℝ)
    (hw : ∀ a ∈ activities, 0 ≤ weight a)
    (hsupport : ∀ a ∈ activities, support a ⊆ pivots)
    (heps : 0 ≤ eps)
    (hepsc : eps ≤ c)
    (hzero : ∀ p ∈ pivots, T 0 p = 0)
    (hrec : ∀ n p, p ∈ pivots →
      T (n + 1) p ≤
        ∑ a ∈ activities,
          if p ∈ support a then
            weight a *
              Real.exp (∑ q ∈ support a, T n q)
          else 0)
    (hcharged : ∀ p, p ∈ pivots →
      (∑ a ∈ activities,
        if p ∈ support a then
          weight a *
            Real.exp (((support a).card : ℝ) * c)
        else 0) ≤ eps) :
    ∀ n p, p ∈ pivots → T n p ≤ eps := by
  intro n
  induction n with
  | zero =>
      intro p hp
      rw [hzero p hp]
      exact heps
  | succ n ih =>
      intro p hp
      have hraw := hrec n p hp
      have hsum :
          (∑ a ∈ activities,
            if p ∈ support a then
              weight a * Real.exp (∑ q ∈ support a, T n q)
            else 0) ≤
          ∑ a ∈ activities,
            if p ∈ support a then
              weight a * Real.exp (((support a).card : ℝ) * c)
            else 0 := by
        apply Finset.sum_le_sum
        intro a ha
        by_cases hpa : p ∈ support a
        · simp only [hpa, if_true]
          have hinside :
              (∑ q ∈ support a, T n q) ≤
                ((support a).card : ℝ) * c := by
            calc
              (∑ q ∈ support a, T n q) ≤
                  ∑ q ∈ support a, c := by
                    apply Finset.sum_le_sum
                    intro q hq
                    have hqp : q ∈ pivots := hsupport a ha hq
                    exact (ih q hqp).trans hepsc
              _ = ((support a).card : ℝ) * c := by simp
          have hexp :
              Real.exp (∑ q ∈ support a, T n q) ≤
                Real.exp (((support a).card : ℝ) * c) :=
            Real.exp_le_exp.mpr hinside
          exact mul_le_mul_of_nonneg_left hexp (hw a ha)
        · simp [hpa]
      exact hraw.trans (hsum.trans (hcharged p hp))

/-- If the charged row is below both the branch reserve `c` and the desired KP
size coefficient `alpha`, then every finite tree depth is already below the KP
per-pivot target `alpha`. -/
theorem charged_activity_row_closes_kp_tree_budget
    {A P : Type*} [DecidableEq A] [DecidableEq P]
    (activities : Finset A)
    (pivots : Finset P)
    (support : A → Finset P)
    (weight : A → ℝ)
    (T : ℕ → P → ℝ)
    (c eps alpha : ℝ)
    (hw : ∀ a ∈ activities, 0 ≤ weight a)
    (hsupport : ∀ a ∈ activities, support a ⊆ pivots)
    (heps : 0 ≤ eps)
    (hepsc : eps ≤ c)
    (hepsalpha : eps ≤ alpha)
    (hzero : ∀ p ∈ pivots, T 0 p = 0)
    (hrec : ∀ n p, p ∈ pivots →
      T (n + 1) p ≤
        ∑ a ∈ activities,
          if p ∈ support a then
            weight a *
              Real.exp (∑ q ∈ support a, T n q)
          else 0)
    (hcharged : ∀ p, p ∈ pivots →
      (∑ a ∈ activities,
        if p ∈ support a then
          weight a *
            Real.exp (((support a).card : ℝ) * c)
        else 0) ≤ eps) :
    ∀ n p, p ∈ pivots → T n p ≤ alpha := by
  intro n p hp
  exact (charged_activity_row_closes_vector_tree_recursion
    activities pivots support weight T c eps hw hsupport heps hepsc
    hzero hrec hcharged n p hp).trans hepsalpha

#print axioms union_support_charge_le_total_incidence_charge
#print axioms incidence_charge_exact_split
#print axioms charged_activity_row_closes_vector_tree_recursion
#print axioms charged_activity_row_closes_kp_tree_budget

end Millennium.YangMills
