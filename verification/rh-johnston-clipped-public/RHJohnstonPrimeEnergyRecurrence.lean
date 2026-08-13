import Mathlib

namespace RHJohnstonPrimeEnergyRecurrence

/-- Negative Johnston integral deficit at an endpoint, normalized by removing
the square distance from the frozen Chebyshev prefix. -/
noncomputable def energy (F p theta : ℝ) : ℝ :=
  -F - (p - theta)^2 / 2

/-- Exact propagation of the Johnston integral across one prime gap when theta
is frozen at `theta`. -/
noncomputable def propagateIntegral (F p q theta : ℝ) : ℝ :=
  F + theta * (q - p) - (q^2 - p^2) / 2

/-- After reaching the next prime `q`, theta jumps by `ell = log q` while the
integral stays continuous.  The normalized energy increment is exactly
`ell*(q-theta)-ell^2/2`, independent of the previous endpoint `p` and integral
value `F`. -/
theorem energy_recurrence
    {F p q theta ell : ℝ} :
    energy (propagateIntegral F p q theta) q (theta + ell) -
      energy F p theta
      = ell * (q - theta) - ell^2 / 2 := by
  unfold energy propagateIntegral
  ring

/-- Strict growth is therefore equivalent to the one-step prime-prefix
inequality `ell/2 < q-theta` when `ell>0`. -/
theorem energy_strictly_grows_iff
    {F p q theta ell : ℝ} (hell : 0 < ell) :
    energy F p theta < energy (propagateIntegral F p q theta) q (theta + ell) ↔
      ell / 2 < q - theta := by
  have hrec := energy_recurrence (F := F) (p := p) (q := q)
    (theta := theta) (ell := ell)
  constructor
  · intro hg
    have hdiff : 0 < ell * (q - theta) - ell^2 / 2 := by
      linarith
    by_contra hnot
    have hle : q - theta ≤ ell / 2 := le_of_not_gt hnot
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hell)
    nlinarith
  · intro h
    have hmul := mul_lt_mul_of_pos_left h hell
    have hdiff : 0 < ell * (q - theta) - ell^2 / 2 := by
      nlinarith
    linarith

/-- The same recurrence rewritten as a finite random-walk update. -/
theorem energy_next_value
    {F p q theta ell : ℝ} :
    energy (propagateIntegral F p q theta) q (theta + ell) =
      energy F p theta + ell * (q - theta) - ell^2 / 2 := by
  have h := energy_recurrence (F := F) (p := p) (q := q)
    (theta := theta) (ell := ell)
  linarith

/-- In the left-clipped regime, add the endpoint square penalty. -/
noncomputable def leftClippedEnergy (E p theta : ℝ) : ℝ :=
  E + (p - theta)^2 / 2

/-- Exact adjacent-gap algebra.  When both stages are genuinely left-clipped,
this is exactly the increment of the clipped Johnston gap minimum; the
logarithmic jump cancels completely. -/
theorem left_clipped_increment_identity
    {E p q theta ell : ℝ} :
    leftClippedEnergy (E + ell * (q - theta) - ell^2 / 2) q (theta + ell) -
      leftClippedEnergy E p theta
      = (q - p) * (p + q - 2 * theta) / 2 := by
  unfold leftClippedEnergy
  ring

/-- If `theta ≤ p < q` and the next prefix remains left of `q`, then the actual
left-clipped scalar grows strictly.  The `theta+ell ≤ q` hypothesis records the
regime boundary even though the final algebraic sign no longer depends on
`ell`. -/
theorem left_clipped_strict_growth
    {E p q theta ell : ℝ}
    (hpq : p < q) (htheta : theta ≤ p) (_hnext : theta + ell ≤ q) :
    leftClippedEnergy E p theta <
      leftClippedEnergy (E + ell * (q - theta) - ell^2 / 2) q (theta + ell) := by
  have hgap : 0 < q - p := sub_pos.mpr hpq
  have hmid : 0 < p + q - 2 * theta := by linarith
  have hprod : 0 < (q - p) * (p + q - 2 * theta) / 2 := by positivity
  have hid := left_clipped_increment_identity
    (E := E) (p := p) (q := q) (theta := theta) (ell := ell)
  linarith

/-- Telescoping interface: any finite chain obeying the prime-energy update has
terminal energy equal to initial energy plus the sum of its increments. -/
theorem telescope_energy_updates
    (E jump : ℕ → ℝ)
    (hstep : ∀ n, E (n + 1) = E n + jump n) :
    ∀ N, E N = E 0 + ∑ n ∈ Finset.range N, jump n := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [hstep N, ih, Finset.sum_range_succ]
      ring

#print axioms energy_recurrence
#print axioms energy_strictly_grows_iff
#print axioms energy_next_value
#print axioms left_clipped_increment_identity
#print axioms left_clipped_strict_growth
#print axioms telescope_energy_updates

end RHJohnstonPrimeEnergyRecurrence
