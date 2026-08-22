import Mathlib

/-!
# Navier--Stokes atomic / Type-I finite firewalls

Finite real algebra only.

These declarations formalize two scalar shadows used in the research audit:

1. a positive point-mass lower bound cannot coexist at every small scale with a
   linear local-energy upper bound `m <= M*r`;
2. a uniformly bounded first-order spectral budget does not, by itself, bound a
   second-order spectral budget.

They do not formalize endpoint measures, Albritton--Barker Type I, Huang's Oseen
operators, Navier--Stokes, or any Clay theorem.
-/

namespace NSAtomicTypeISplit

/-- Scalar shadow of the measure-theoretic fact that an all-scale local energy
bound of order `O(r)` excludes a positive point atom. -/
theorem linear_scale_bound_excludes_positive_atom
    (M m : ℝ) (hM : 0 ≤ M) (hm : 0 < m) :
    ¬ (∀ r : ℝ, 0 < r → m ≤ M * r) := by
  intro h
  let r : ℝ := m / (2 * (M + 1))
  have hMp : 0 < M + 1 := by linarith
  have hden : 0 < 2 * (M + 1) := by positivity
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos hm hden
  have hbound : m ≤ M * r := h r hr
  have hfrac : M / (2 * (M + 1)) < 1 := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hlt : M * r < m := by
    calc
      M * r = m * (M / (2 * (M + 1))) := by
        dsimp [r]
        ring
      _ < m * 1 := mul_lt_mul_of_pos_left hfrac hm
      _ = m := by ring
  linarith

/-- A slightly more local form: once a scale has `M*r < m`, the linear
local-energy budget and an atom-mass lower bound are incompatible. -/
theorem one_small_scale_excludes_atom
    (M m r : ℝ)
    (hsmall : M * r < m)
    (hatom : m ≤ M * r) : False := by
  linarith

/-- One scalar spectral mode with spectral value `N` and amplitude `1/N` has
first-order quadratic cost `1/N` but second-order quadratic cost `1`.
This is only an abstract spectral bookkeeping identity. -/
theorem one_mode_first_second_order_separation
    (N : ℝ) (hN : 0 < N) :
    N * (1 / N) ^ 2 = 1 / N ∧
      N ^ 2 * (1 / N) ^ 2 = 1 := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  constructor
  · field_simp [hN0]
  · field_simp [hN0]

/-- `k` identical abstract modes at spectral value `k` and amplitude `1/k`
have total first-order cost exactly `1`, while the second-order cost is `k`.
Thus a fixed first-order budget is compatible with arbitrarily large finite
second-order budget. -/
theorem finite_mode_first_second_order_budget
    (k : ℕ) (hk : 0 < k) :
    let N : ℝ := k
    N * (N * (1 / N) ^ 2) = 1 ∧
      N * (N ^ 2 * (1 / N) ^ 2) = N := by
  dsimp
  have hN0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk
  constructor
  · field_simp [hN0]
  · field_simp [hN0]

#print axioms linear_scale_bound_excludes_positive_atom
#print axioms one_small_scale_excludes_atom
#print axioms one_mode_first_second_order_separation
#print axioms finite_mode_first_second_order_budget

end NSAtomicTypeISplit
