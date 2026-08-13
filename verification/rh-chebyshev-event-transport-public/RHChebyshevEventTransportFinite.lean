import Mathlib

namespace RHChebyshevEventTransportFinite

/-!
# Finite event-transport algebra for the critical weighted-Chebyshev margin

At a prime-power event of location `n`, write

* `u = sqrt(theta_before)`,
* `v = sqrt(theta_after)`,
* `q = sqrt(n)`,
* `w` for the event's von-Mangoldt mass,
* `A` for the weighted prefix before the event.

The critical potential is `2*sqrt(theta) - A - c`. Since the event changes
`theta` by `w` and `A` by `w/q`, its exact increment is

  w * (2/(u+v) - 1/q).

This file verifies only that finite algebra and its sign consequences. It does
not define primes, Chebyshev theta, von Mangoldt, square roots, Johnston's
criterion, zeta, or RH.
-/

/-- Abstract critical potential in square-root mass coordinate. -/
def potential (u A c : ℝ) : ℝ := 2 * u - A - c

/-- Exact event increment after rationalizing `v-u` using
`v^2-u^2=w`. -/
theorem event_increment_identity
    {u v q w A c : ℝ}
    (_hq : q ≠ 0) (huv : u + v ≠ 0)
    (hmass : v ^ 2 = u ^ 2 + w) :
    potential v (A + w / q) c - potential u A c =
      w * (2 / (u + v) - 1 / q) := by
  have hdiff : (v - u) * (u + v) = w := by
    nlinarith
  have hrat : v - u = w / (u + v) := by
    exact (eq_div_iff huv).2 hdiff
  unfold potential
  calc
    2 * v - (A + w / q) - c - (2 * u - A - c) =
        2 * (v - u) - w / q := by ring
    _ = 2 * (w / (u + v)) - w / q := by rw [hrat]
    _ = w * (2 / (u + v) - 1 / q) := by ring

/-- With positive event mass and positive coordinates, the critical potential
increases exactly when the event location satisfies the midpoint condition
`u+v <= 2q`. -/
theorem event_increment_nonneg_iff_midpoint
    {u v q w A c : ℝ}
    (hq : 0 < q) (huv : 0 < u + v) (hw : 0 < w)
    (hmass : v ^ 2 = u ^ 2 + w) :
    0 ≤ potential v (A + w / q) c - potential u A c ↔
      u + v ≤ 2 * q := by
  rw [event_increment_identity (ne_of_gt hq) (ne_of_gt huv) hmass]
  constructor
  · intro h
    let k : ℝ := 2 / (u + v) - 1 / q
    have hkernel : 0 ≤ k := by
      by_contra hk
      have hkneg : k < 0 := lt_of_not_ge hk
      have hprodneg : w * k < 0 := mul_neg_of_pos_of_neg hw hkneg
      dsimp [k] at hprodneg
      linarith
    dsimp [k] at hkernel
    have hfrac : 1 / q ≤ 2 / (u + v) := sub_nonneg.mp hkernel
    simpa using (div_le_div_iff₀ hq huv).mp hfrac
  · intro hmid
    have hcross : 1 * (u + v) ≤ 2 * q := by simpa using hmid
    have hfrac : 1 / q ≤ 2 / (u + v) :=
      (div_le_div_iff₀ hq huv).mpr hcross
    have hkernel : 0 ≤ 2 / (u + v) - 1 / q := sub_nonneg.mpr hfrac
    exact mul_nonneg (le_of_lt hw) hkernel

/-- The corresponding strict version: the potential drops at an event exactly
when the square-root mass midpoint lies strictly to the right of the event's
square-root location. -/
theorem event_increment_neg_iff_midpoint
    {u v q w A c : ℝ}
    (hq : 0 < q) (huv : 0 < u + v) (hw : 0 < w)
    (hmass : v ^ 2 = u ^ 2 + w) :
    potential v (A + w / q) c - potential u A c < 0 ↔
      2 * q < u + v := by
  have hnon := event_increment_nonneg_iff_midpoint
    (A := A) (c := c) hq huv hw hmass
  constructor
  · intro hneg
    by_contra hnot
    have hmid : u + v ≤ 2 * q := le_of_not_gt hnot
    have hge := hnon.mpr hmid
    linarith
  · intro hmid
    by_contra hnot
    have hge : 0 ≤ potential v (A + w / q) c - potential u A c :=
      le_of_not_gt hnot
    have hle := hnon.mp hge
    linarith

/-- A useful sufficient condition: if both cumulative Chebyshev square-root
coordinates are no larger than the event location square root, then the event
cannot decrease the critical potential. -/
theorem delayed_mass_event_nondecreasing
    {u v q w A c : ℝ}
    (hq : 0 < q) (huv : 0 < u + v) (hw : 0 < w)
    (hu : u ≤ q) (hv : v ≤ q)
    (hmass : v ^ 2 = u ^ 2 + w) :
    potential u A c ≤ potential v (A + w / q) c := by
  have hmid : u + v ≤ 2 * q := by linarith
  have hnon := (event_increment_nonneg_iff_midpoint
    (A := A) (c := c) hq huv hw hmass).mpr hmid
  linarith

/-- Exact finite telescoping interface for any sequence of event increments. -/
theorem telescoping_potential
    (P : ℕ → ℝ) :
    ∀ n, P n - P 0 = ∑ k ∈ Finset.range n, (P (k + 1) - P k) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      ring

#print axioms event_increment_identity
#print axioms event_increment_nonneg_iff_midpoint
#print axioms event_increment_neg_iff_midpoint
#print axioms delayed_mass_event_nondecreasing
#print axioms telescoping_potential

end RHChebyshevEventTransportFinite
