import Mathlib

namespace Millennium.SourceCutCEGAR.FiniteHorizonCohomology

open scoped BigOperators

/-- `weightedPrefix a n` is the unnormalized finite-horizon potential
`sum_{k<n} (n-1-k) a_k`, written recursively. -/
def weightedPrefix (a : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => weightedPrefix a n + ∑ k ∈ Finset.range n, a k

/-- Split a prefix into its zeroth term and the shifted remaining prefix. -/
theorem zero_add_shiftedPrefix (a : ℕ → ℚ) (n : ℕ) :
    a 0 + ∑ k ∈ Finset.range n, a (k + 1) =
      ∑ k ∈ Finset.range (n + 1), a k := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        a 0 + ∑ k ∈ Finset.range (n + 1), a (k + 1) =
            (a 0 + ∑ k ∈ Finset.range n, a (k + 1)) + a (n + 1) := by
              rw [Finset.sum_range_succ]
              ring
        _ = (∑ k ∈ Finset.range (n + 1), a k) + a (n + 1) := by rw [ih]
        _ = ∑ k ∈ Finset.range (n + 2), a k := by
              simp [Finset.sum_range_succ, add_assoc]

/-- Exact unnormalized telescope behind the finite-horizon cohomology
exactifier. -/
theorem weightedPrefix_shift_identity (a : ℕ → ℚ) (n : ℕ) :
    (n : ℚ) * a 0 + weightedPrefix (fun k => a (k + 1)) n - weightedPrefix a n =
      ∑ k ∈ Finset.range n, a k := by
  induction n with
  | zero => simp [weightedPrefix]
  | succ n ih =>
      simp only [weightedPrefix, Nat.cast_add, Nat.cast_one]
      have hshift := zero_add_shiftedPrefix a n
      rw [Finset.sum_range_succ] at hshift ⊢
      linarith

/-- Normalized finite-horizon cohomology exactifier. A positive `n`-block
average is exactly the one-step defect after adding the explicit weighted
prefix coboundary. -/
theorem finiteHorizon_coboundary_exactifier
    (a : ℕ → ℚ) (n : ℕ) (hn : 0 < n) :
    a 0 + weightedPrefix (fun k => a (k + 1)) n / (n : ℚ) -
        weightedPrefix a n / (n : ℚ) =
      (∑ k ∈ Finset.range n, a k) / (n : ℚ) := by
  have hn0 : (n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have h := weightedPrefix_shift_identity a n
  field_simp [hn0]
  linarith

/-- A positive block average becomes a positive one-step corrected defect. -/
theorem finiteHorizon_positive_block_to_pointwise
    (a : ℕ → ℚ) (n : ℕ) (hn : 0 < n) (η : ℚ)
    (hblock : (∑ k ∈ Finset.range n, a k) / (n : ℚ) ≥ η) :
    a 0 + weightedPrefix (fun k => a (k + 1)) n / (n : ℚ) -
        weightedPrefix a n / (n : ℚ) ≥ η := by
  rw [finiteHorizon_coboundary_exactifier a n hn]
  exact hblock

/-- Pure coboundaries telescope to zero around a two-cycle. -/
theorem twoCycle_coboundary_sum_zero
    (h0 h1 : ℚ) :
    (h1 - h0) + (h0 - h1) = 0 := by
  ring

/-- Statewise menu positivity does not imply invariant-cycle positivity. -/
theorem statewise_menu_firewall :
    max (1 : ℚ) (-2) > 0 ∧
    max (-2 : ℚ) 1 > 0 ∧
    ((1 : ℚ) + (-2)) / 2 < 0 ∧
    ((-2 : ℚ) + 1) / 2 < 0 := by
  norm_num

#print axioms zero_add_shiftedPrefix
#print axioms weightedPrefix_shift_identity
#print axioms finiteHorizon_coboundary_exactifier
#print axioms finiteHorizon_positive_block_to_pointwise
#print axioms twoCycle_coboundary_sum_zero
#print axioms statewise_menu_firewall

end Millennium.SourceCutCEGAR.FiniteHorizonCohomology
