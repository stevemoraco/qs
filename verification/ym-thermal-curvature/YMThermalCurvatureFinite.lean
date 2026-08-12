import Mathlib

/-!
# Yang--Mills thermal-curvature firewall: finite scalar core

## Honesty boundary

This file proves finite identities for a discrete endpoint ledger and a
two-mode positive scalar correlation model. It does **not** formalize infinite
series, limiting spectral measures, Hamiltonians, transfer operators,
Osterwalder--Schrader reconstruction, lattice gauge theory, continuum limits,
compact gauge groups, or Yang--Mills.

In particular, the finite telescope below does not justify passage from a
finite curvature sum to an infinite tail. Such a passage needs a separate
summability and uniform-tail theorem.
-/

namespace Millennium
namespace YangMills
namespace ThermalCurvatureFinite

/-- The discrete curvature of an endpoint sequence: the loss from one index to
the next. -/
def discreteCurvature (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  d n - d (n + 1)

/-- Exact finite endpoint identity. Starting at index `n`, subtracting the
first `N` discrete curvatures leaves exactly the endpoint `d (n + N)`.
No infinite summation or limit is present. -/
theorem finite_endpoint_telescope (d : ℕ → ℝ) (n N : ℕ) :
    d n - ∑ j in Finset.range N, discreteCurvature d (n + j) =
      d (n + N) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      calc
        d n -
              ((∑ j in Finset.range N, discreteCurvature d (n + j)) +
                discreteCurvature d (n + N)) =
            (d n - ∑ j in Finset.range N, discreteCurvature d (n + j)) -
              discreteCurvature d (n + N) := by ring
        _ = d (n + N) - discreteCurvature d (n + N) := by rw [ih]
        _ = d (n + N + 1) := by simp [discreteCurvature]
        _ = d (n + N.succ) := by simp

/-- Equivalent finite sum form of the endpoint identity. -/
theorem finite_curvature_sum (d : ℕ → ℝ) (n N : ℕ) :
    (∑ j in Finset.range N, discreteCurvature d (n + j)) =
      d n - d (n + N) := by
  have h := finite_endpoint_telescope d n N
  linarith

/-- Algebraic defect identity for a two-mode positive correlation.

Think of `x, y` as the two current mode weights, `r, q` as one-step
transfer factors, and `w` as a multiplicity. The identity is polynomial and
does not use spectral theory. -/
theorem two_mode_cross_product_identity (w x y r q : ℝ) :
    (x + w * y) * (x * r ^ 2 + w * y * q ^ 2) -
        (x * r + w * y * q) ^ 2 =
      w * x * y * (r - q) ^ 2 := by
  ring

/-- Nonnegative weights make the two-mode three-point sequence log-convex at
the cross-product level. -/
theorem two_mode_cross_product_nonnegative
    (w x y r q : ℝ) (hw : 0 ≤ w) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x * r + w * y * q) ^ 2 ≤
      (x + w * y) * (x * r ^ 2 + w * y * q ^ 2) := by
  rw [← sub_nonneg]
  rw [two_mode_cross_product_identity]
  positivity

/-- A positive middle term and a nonnegative cross-product defect imply the
logarithmic cross-ratio has nonnegative sign. -/
theorem log_cross_ratio_nonnegative
    (z0 z1 z2 : ℝ) (hz1 : 0 < z1)
    (hconvex : z1 ^ 2 ≤ z0 * z2) :
    0 ≤ Real.log ((z0 * z2) / z1 ^ 2) := by
  apply Real.log_nonneg
  have hz1sq : 0 < z1 ^ 2 := pow_pos hz1 2
  exact (le_div_iff₀ hz1sq).2 (by simpa using hconvex)

/-- The corresponding finite two-mode logarithmic curvature is nonnegative.
This is a one-index scalar statement, not an infinite-tail estimate. -/
theorem two_mode_log_curvature_nonnegative
    (w x y r q : ℝ)
    (hw : 0 ≤ w) (hx : 0 < x) (hy : 0 ≤ y)
    (hr : 0 < r) (hq : 0 ≤ q) :
    0 ≤ Real.log
      (((x + w * y) * (x * r ^ 2 + w * y * q ^ 2)) /
        (x * r + w * y * q) ^ 2) := by
  apply log_cross_ratio_nonnegative
  · positivity
  · exact two_mode_cross_product_nonnegative w x y r q hw hx.le hy

/-- Exact finite hidden-mode error formula. A mode with coefficient
`1 / (w + 1)` can become invisible in a large-multiplicity snapshot without
being absent at any finite `w`. -/
theorem hidden_mode_bulk_error
    (w x y : ℝ) (hden : w + 1 ≠ 0) :
    (x + w * y) / (w + 1) - y =
      (x - y) / (w + 1) := by
  field_simp [hden]
  ring

/-- At every finite nonnegative multiplicity, the hidden-mode coefficient is
strictly positive. -/
theorem hidden_mode_weight_stays_positive (w : ℝ) (hw : 0 ≤ w) :
    0 < 1 / (w + 1) := by
  positivity

/-- An exact rational snapshot: a mode with transfer factor `3/4` has only
weight `1/100` against 99 bulk modes with transfer factor `1/2`. The
one-step correlation differs from the bulk value by `1/400`, yet the hidden
factor is strictly larger. The three-point cross-product defect is `99/16`.
-/
theorem explicit_hidden_mode_snapshot :
    let w : ℚ := 99
    let hidden : ℚ := 3 / 4
    let bulk : ℚ := 1 / 2
    let c1 := (hidden + w * bulk) / (w + 1)
    let c2 := (hidden ^ 2 + w * bulk ^ 2) / (w + 1)
    bulk < hidden ∧
    0 < 1 / (w + 1) ∧
    c1 = 201 / 400 ∧
    c1 - bulk = 1 / 400 ∧
    c2 = 81 / 320 ∧
    (1 + w) * (hidden ^ 2 + w * bulk ^ 2) -
      (hidden + w * bulk) ^ 2 = 99 / 16 := by
  norm_num

#print axioms finite_endpoint_telescope
#print axioms finite_curvature_sum
#print axioms two_mode_cross_product_identity
#print axioms two_mode_cross_product_nonnegative
#print axioms log_cross_ratio_nonnegative
#print axioms two_mode_log_curvature_nonnegative
#print axioms hidden_mode_bulk_error
#print axioms hidden_mode_weight_stays_positive
#print axioms explicit_hidden_mode_snapshot

end ThermalCurvatureFinite
end YangMills
end Millennium
