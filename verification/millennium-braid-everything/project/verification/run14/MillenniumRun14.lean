import Mathlib

/-!
# Run 14 finite-core verification smoke suite

These theorems are deliberately finite. They exercise the clean GitHub-hosted
Lean/Mathlib fallback and do not prove any Millennium problem.
-/

namespace MillenniumRun14

/-- Finite scalar determinant certificate used by a two-point RH kernel test. -/
theorem rh_two_point_negative_det
    (r x y : ℝ)
    (h : r ^ 2 < x ^ 2 + y ^ 2) :
    r ^ 2 - (x ^ 2 + y ^ 2) < 0 := by
  linarith

/-- One prime-power atom has the wrong sign for the first shifted Hausdorff entry. -/
theorem rh_prime_atom_c00_negative
    (B : ℝ)
    (hB : 0 < B) :
    -B < 0 := by
  linarith

/-- One prime-power atom is also negative in the next normalized derivative entry. -/
theorem rh_prime_atom_c10_negative
    (B ell : ℝ)
    (hB : 0 < B)
    (hell : 0 < ell) :
    -(B / 2) * (1 + ell) < 0 := by
  have hleft : -(B / 2) < 0 := by linarith
  have hright : 0 < 1 + ell := by linarith
  exact mul_neg_of_neg_of_pos hleft hright

/-- The first mixed prime-atom contribution is negative below `ell = 1`. -/
theorem rh_prime_atom_c01_negative_of_lt_one
    (B ell : ℝ)
    (hB : 0 < B)
    (hell : ell < 1) :
    (B / 2) * (ell - 1) < 0 := by
  have hleft : 0 < B / 2 := by linarith
  have hright : ell - 1 < 0 := by linarith
  exact mul_neg_of_pos_of_neg hleft hright

/-- The same contribution is positive above `ell = 1`, proving sign change. -/
theorem rh_prime_atom_c01_positive_of_one_lt
    (B ell : ℝ)
    (hB : 0 < B)
    (hell : 1 < ell) :
    0 < (B / 2) * (ell - 1) := by
  have hleft : 0 < B / 2 := by linarith
  have hright : 0 < ell - 1 := by linarith
  exact mul_pos hleft hright

/-- A fixed positive threshold leaves a nonzero subthreshold region. -/
theorem ns_positive_threshold_has_subthreshold_nonzero
    (τ : ℝ)
    (hτ : 0 < τ) :
    ∃ x : ℝ, 0 < x ∧ x ≤ τ ∧ ¬ (x = 0 ∨ τ < x) := by
  refine ⟨τ / 2, by linarith, by linarith, ?_⟩
  intro hx
  rcases hx with hx | hx
  · linarith
  · linarith

/-- The scalar order relation behind the finite Yang--Mills transfer countermodel. -/
theorem ym_larger_excited_eigenvalue_can_have_smaller_gap
    (δ : ℝ)
    (hδ0 : 0 < δ)
    (hδ : δ < 1 / 2) :
    0 < δ ∧ (1 / 2 : ℝ) ≤ 1 - δ ∧ δ < 1 / 2 := by
  constructor
  · exact hδ0
  constructor <;> linarith

/-- Bounded congestion controls the total number of charged witnesses. -/
theorem pnp_bounded_congestion_sum
    {α β : Type*}
    [DecidableEq α]
    (U : Finset α)
    (fibers : α → Finset β)
    (q : ℕ)
    (h : ∀ u, u ∈ U → (fibers u).card ≤ q) :
    Finset.sum U (fun u => (fibers u).card) ≤ q * U.card := by
  calc
    Finset.sum U (fun u => (fibers u).card) ≤
        Finset.sum U (fun _u => q) := by
      exact Finset.sum_le_sum (fun u hu => h u hu)
    _ = U.card * q := by simp
    _ = q * U.card := Nat.mul_comm _ _

/-- A cohomological idempotent need not preserve a distinguished axis. -/
def hodgeProjector (v : ℚ × ℚ) : ℚ × ℚ :=
  (0, v.1 + v.2)

theorem hodgeProjector_idempotent (v : ℚ × ℚ) :
    hodgeProjector (hodgeProjector v) = hodgeProjector v := by
  rcases v with ⟨x, y⟩
  ext <;> simp [hodgeProjector]

theorem hodgeProjector_moves_designated_axis :
    hodgeProjector (1, 0) = (0, 1) := by
  norm_num [hodgeProjector]

/-- Finite rearrangement behind a BSD pairing/discriminant index budget. -/
theorem bsd_discriminant_index_rearrangement
    (ell r c d d' : ℤ)
    (h : 2 * ell = r * c + d - d') :
    2 * ell + d' = r * c + d := by
  omega

/-- Finite length correction: cokernel, kernel, and free-lattice index all matter. -/
theorem bsd_control_length_correction
    (tM tN c k i : ℤ)
    (h : c = tN - tM + k + i) :
    tN - tM = c - k - i := by
  omega

end MillenniumRun14
