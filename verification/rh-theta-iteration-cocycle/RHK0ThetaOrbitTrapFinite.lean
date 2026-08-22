import Mathlib

/-!
# RH K0 theta-orbit trap finite/order core

HONESTY BOUNDARY

This file verifies only an abstract order-theoretic lemma used by the
paper-level Chebyshev self-map argument:

* one point lying between consecutive states of a monotone state-map orbit is
  mapped above itself;
* if such orbit intervals cover a whole tail, the state map lies above the
  diagonal on that tail;
* arbitrarily late strict downcrossings contradict such a tail cover.

It does not formalize primes, the Chebyshev theta function, K0, Littlewood's
oscillation theorem, primorial fixed points, zeta zeros, RH, or an official
Clay statement.
-/

namespace MillenniumBraid
namespace RHK0ThetaOrbitTrapFinite

/-- A point trapped between consecutive states of a monotone orbit is sent
above itself by the state map. -/
theorem interval_point_maps_above
    (T : ℝ → ℝ)
    (x : ℕ → ℝ)
    (hT : Monotone T)
    (hrec : ∀ n, x (n + 1) = T (x n))
    {n : ℕ}
    {y : ℝ}
    (hleft : x n ≤ y)
    (hright : y ≤ x (n + 1)) :
    y ≤ T y := by
  calc
    y ≤ x (n + 1) := hright
    _ = T (x n) := hrec n
    _ ≤ T y := hT hleft

/-- If consecutive orbit intervals cover every point beyond the initial
state, the monotone map remains above the diagonal on that entire tail. -/
theorem tail_above_diagonal_of_interval_cover
    (T : ℝ → ℝ)
    (x : ℕ → ℝ)
    (hT : Monotone T)
    (hrec : ∀ n, x (n + 1) = T (x n))
    (hcover : ∀ y, x 0 ≤ y → ∃ n, x n ≤ y ∧ y ≤ x (n + 1)) :
    ∀ y, x 0 ≤ y → y ≤ T y := by
  intro y hy
  obtain ⟨n, hleft, hright⟩ := hcover y hy
  exact interval_point_maps_above T x hT hrec hleft hright

/-- Arbitrarily late strict downcrossings are incompatible with a monotone
orbit whose consecutive intervals cover a tail. -/
theorem no_tail_cover_with_arbitrarily_late_downcrossings
    (T : ℝ → ℝ)
    (x : ℕ → ℝ)
    (hT : Monotone T)
    (hrec : ∀ n, x (n + 1) = T (x n))
    (hcover : ∀ y, x 0 ≤ y → ∃ n, x n ≤ y ∧ y ≤ x (n + 1))
    (hdown : ∀ A, ∃ y, A ≤ y ∧ T y < y) :
    False := by
  obtain ⟨y, hy, hstrict⟩ := hdown (x 0)
  have habove : y ≤ T y :=
    tail_above_diagonal_of_interval_cover T x hT hrec hcover y hy
  linarith

/-- Contrapositive packaging: under arbitrary late downcrossings, no orbit
interval family can cover the whole tail. -/
theorem late_downcrossings_force_uncovered_tail_point
    (T : ℝ → ℝ)
    (x : ℕ → ℝ)
    (hT : Monotone T)
    (hrec : ∀ n, x (n + 1) = T (x n))
    (hdown : ∀ A, ∃ y, A ≤ y ∧ T y < y) :
    ¬ (∀ y, x 0 ≤ y → ∃ n, x n ≤ y ∧ y ≤ x (n + 1)) := by
  intro hcover
  exact no_tail_cover_with_arbitrarily_late_downcrossings
    T x hT hrec hcover hdown

#print axioms interval_point_maps_above
#print axioms tail_above_diagonal_of_interval_cover
#print axioms no_tail_cover_with_arbitrarily_late_downcrossings
#print axioms late_downcrossings_force_uncovered_tail_point

end RHK0ThetaOrbitTrapFinite
end MillenniumBraid
