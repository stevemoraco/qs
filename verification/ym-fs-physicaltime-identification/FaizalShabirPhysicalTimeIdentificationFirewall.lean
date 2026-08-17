import Mathlib

/-!
# Faizal--Shabir physical-time identification firewalls

Finite scalar logic extracted from a hostile audit of arXiv:2606.19362v1.

The file formalizes only:

* additive summable/telescoping-style control does not itself force two
  trajectories to coincide;
* a scale-correct sign-free normalized transfer recurrence once an analytic
  operator estimate supplies the combined norm defect;
* a concrete invariant normalized tube at blocking power two;
* finite physical-time accumulation: `n` one-slice discrepancies of size
  `rate * a` cost at most `rate * t` when `n*a <= t`;
* an order-`a` one-step discrepancy can therefore accumulate to an order-one
  physical-time discrepancy, so continuum identification needs `o(a)` (or an
  equivalent generator/semigroup comparison), not merely `o(1)` one-step
  closeness.

This file does not formalize Hilbert-space operator norms, the Faizal--Shabir
RG map, lattice Yang--Mills, Osterwalder--Schrader reconstruction, a mass gap,
or the Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirPhysicalTimeIdentificationFirewall

/-- Constant unit separation: an additive recurrence with zero defect can hold
at every step without the distance ever tending to zero. -/
def constantDistance (_k : ℕ) : ℝ := 1

/-- Zero additive defect. -/
def zeroDefect (_k : ℕ) : ℝ := 0

/-- The displayed additive comparison `d_{k+1} <= d_k + eps_k` is compatible
with a permanently nonzero distance, even with identically zero defects. -/
theorem additive_recurrence_does_not_force_vanishing (k : ℕ) :
    constantDistance (k + 1) ≤ constantDistance k + zeroDefect k := by
  norm_num [constantDistance, zeroDefect]

/-- The same countermodel never identifies the two trajectories. -/
theorem additive_countermodel_stays_separated (k : ℕ) :
    constantDistance k = 1 := by
  rfl

/-- A lower scalar/operator-order comparison cannot be used as an upper
Rayleigh comparison.  This is the one-dimensional direction shadow. -/
theorem lower_order_is_not_upper_order :
    (0 : ℝ) ≤ 1 ∧ ¬ ((1 : ℝ) ≤ 0) := by
  norm_num

/--
Scale-correct sign-free normalization shadow.

Think of `lamNext <= lam^b + defect` as the excited-sector operator-norm
consequence of

`T_next = V* T^b V - D + E`

with `defect = ||D|| + ||E||`; no sign of `D` is used.  If the physical
normalization weights obey `wNext = w^b`, then the normalized quantity obeys

`qNext <= q^b + wNext * defect`.
-/
theorem normalized_sign_free_step
    (b : ℕ) (w lam lamNext defect : ℝ)
    (hw : 0 ≤ w)
    (hstep : lamNext ≤ lam ^ b + defect) :
    w ^ b * lamNext ≤ (w * lam) ^ b + w ^ b * defect := by
  have hwb : 0 ≤ w ^ b := pow_nonneg hw b
  have hmul := mul_le_mul_of_nonneg_left hstep hwb
  calc
    w ^ b * lamNext ≤ w ^ b * (lam ^ b + defect) := hmul
    _ = (w * lam) ^ b + w ^ b * defect := by ring

/-- Any normalized one-step majorant closes an invariant tube once its whole
right-hand side is below the tube radius. -/
theorem normalized_tube_from_budget
    (qNext qPow normalizedDefect radius : ℝ)
    (hstep : qNext ≤ qPow + normalizedDefect)
    (hbudget : qPow + normalizedDefect ≤ radius) :
    qNext ≤ radius :=
  hstep.trans hbudget

/-- Concrete power-two invariant tube: `q <= 1/2` and normalized defect
`<= 1/4` imply `qNext <= 1/2` from `qNext <= q^2 + defect`. -/
theorem half_tube_power_two
    (q qNext normalizedDefect : ℝ)
    (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2)
    (hdefect : normalizedDefect ≤ 1 / 4)
    (hstep : qNext ≤ q ^ 2 + normalizedDefect) :
    qNext ≤ 1 / 2 := by
  have hhalfminus : 0 ≤ (1 / 2 : ℝ) - q := sub_nonneg.mpr hq
  have hprod : 0 ≤ q * ((1 / 2 : ℝ) - q) :=
    mul_nonneg hq0 hhalfminus
  nlinarith

/-- Finite additive telescoping with a common one-step discrepancy. -/
theorem finite_additive_telescope
    (D : ℕ → ℝ) (step : ℝ)
    (h0 : D 0 ≤ 0)
    (hstep : ∀ k : ℕ, D (k + 1) ≤ D k + step) :
    ∀ n : ℕ, D n ≤ (n : ℝ) * step := by
  intro n
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      calc
        D (n + 1) ≤ D n + step := hstep n
        _ ≤ (n : ℝ) * step + step := add_le_add_right ih step
        _ = ((n + 1 : ℕ) : ℝ) * step := by
          rw [Nat.cast_add, Nat.cast_one]
          ring

/--
Physical-time accumulation firewall.

If every one-slice discrepancy is at most `rate * a`, then over `n` slices
covering physical time at most `t` the accumulated discrepancy is at most
`rate * t`.  Therefore a family with `rate -> 0` gives a genuine vanishing
fixed-physical-time comparison.
-/
theorem physical_time_telescope
    (D : ℕ → ℝ) (rate a t : ℝ) (n : ℕ)
    (h0 : D 0 ≤ 0)
    (hrate : 0 ≤ rate)
    (hstep : ∀ k : ℕ, D (k + 1) ≤ D k + rate * a)
    (htime : (n : ℝ) * a ≤ t) :
    D n ≤ rate * t := by
  have htel : D n ≤ (n : ℝ) * (rate * a) :=
    finite_additive_telescope D (rate * a) h0 hstep n
  have hmul : rate * ((n : ℝ) * a) ≤ rate * t :=
    mul_le_mul_of_nonneg_left htime hrate
  calc
    D n ≤ (n : ℝ) * (rate * a) := htel
    _ = rate * ((n : ℝ) * a) := by ring
    _ ≤ rate * t := hmul

/-- Exact finite witness that merely `O(a)` one-step closeness need not vanish
at fixed physical time: if `n*a = 1`, then `n` discrepancies of size `c*a`
accumulate to exactly `c`. -/
theorem order_a_step_error_can_accumulate_to_order_one
    (n : ℕ) (a c : ℝ)
    (hunit : (n : ℝ) * a = 1) :
    (n : ℝ) * (c * a) = c := by
  calc
    (n : ℝ) * (c * a) = c * ((n : ℝ) * a) := by ring
    _ = c := by rw [hunit, mul_one]

#print axioms additive_recurrence_does_not_force_vanishing
#print axioms additive_countermodel_stays_separated
#print axioms lower_order_is_not_upper_order
#print axioms normalized_sign_free_step
#print axioms normalized_tube_from_budget
#print axioms half_tube_power_two
#print axioms finite_additive_telescope
#print axioms physical_time_telescope
#print axioms order_a_step_error_can_accumulate_to_order_one

end Millennium.YangMills.FaizalShabirPhysicalTimeIdentificationFirewall
