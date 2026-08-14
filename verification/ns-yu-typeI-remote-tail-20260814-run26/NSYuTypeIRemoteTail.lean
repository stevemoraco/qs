import Mathlib

/-!
# Navier--Stokes / Yu far-field Type-I remote-tail finite core

Finite real algebra only.  This file does **not** formalize the Navier--Stokes
PDE, Yu's filtered-vorticity theorem, the Calderon--Zygmund kernel, the
fixed-annulus integration-by-parts argument, Type-I compactness, or any Clay
conclusion.

It formalizes the reusable scalar endgame behind the following human theorem
interface: after a fixed-annulus integration by parts moves curl from filtered
vorticity onto a degree -3 strain kernel, a Type-I local-energy bound gives a
normalized shell-work gain of order `4^{-m}` at dyadic lag `m`.  Hence shells
beyond lag `M` have a geometric tail of order `4^{-M}`.
-/

noncomputable section

namespace NSYuTypeIRemoteTail

/-- The finite geometric prefix `1 + 1/4 + ... + (1/4)^(n-1)`. -/
def quarterPrefix : Nat → ℝ
  | 0 => 0
  | n + 1 => quarterPrefix n + (1 / 4 : ℝ) ^ n

/-- Exact finite geometric-prefix formula. -/
theorem quarterPrefix_formula (n : Nat) :
    quarterPrefix n = (4 / 3 : ℝ) * (1 - (1 / 4 : ℝ) ^ n) := by
  induction n with
  | zero => norm_num [quarterPrefix]
  | succ n ih =>
      rw [quarterPrefix, ih, pow_succ]
      ring

/-- Every finite quarter-geometric prefix is bounded by `4/3`. -/
theorem quarterPrefix_le_four_thirds (n : Nat) :
    quarterPrefix n ≤ (4 / 3 : ℝ) := by
  rw [quarterPrefix_formula]
  have hp : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
  nlinarith

/-- A finite quarter-geometric tail beginning at dyadic lag `M`. -/
def quarterTail (M n : Nat) : ℝ :=
  (1 / 4 : ℝ) ^ M * quarterPrefix n

/-- The exact finite tail is bounded by `(4/3) 4^{-M}`. -/
theorem quarterTail_le (M n : Nat) :
    quarterTail M n ≤ (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ M := by
  unfold quarterTail
  have hpow : 0 ≤ (1 / 4 : ℝ) ^ M := by positivity
  have h := mul_le_mul_of_nonneg_left (quarterPrefix_le_four_thirds n) hpow
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- If each remote-shell work term has the normalized quarter-lag envelope,
then any finite remote tail inherits the geometric `4^{-M}` bound. -/
theorem remote_tail_work_bound
    (C energy reservoir tailWork : ℝ) (M n : Nat)
    (hC : 0 ≤ C) (hE : 0 ≤ energy) (hR : 0 ≤ reservoir)
    (hwork : tailWork ≤ C * energy * reservoir * quarterTail M n) :
    tailWork ≤
      (4 / 3 : ℝ) * C * energy * reservoir * (1 / 4 : ℝ) ^ M := by
  have hcoef : 0 ≤ C * energy * reservoir := by positivity
  have htail := mul_le_mul_of_nonneg_left (quarterTail_le M n) hcoef
  calc
    tailWork ≤ C * energy * reservoir * quarterTail M n := hwork
    _ ≤ C * energy * reservoir * ((4 / 3 : ℝ) * (1 / 4 : ℝ) ^ M) := by
      simpa [mul_assoc] using htail
    _ = (4 / 3 : ℝ) * C * energy * reservoir * (1 / 4 : ℝ) ^ M := by ring

/-- A strict tail margin closes once the geometric envelope is below the target
margin.  This is the finite scalar absorption step used after the PDE estimates. -/
theorem remote_tail_strict_absorption
    (C energy reservoir tailWork margin : ℝ) (M n : Nat)
    (hC : 0 ≤ C) (hE : 0 ≤ energy) (hR : 0 ≤ reservoir)
    (hwork : tailWork ≤ C * energy * reservoir * quarterTail M n)
    (hsmall :
      (4 / 3 : ℝ) * C * energy * reservoir * (1 / 4 : ℝ) ^ M < margin) :
    tailWork < margin := by
  exact lt_of_le_of_lt
    (remote_tail_work_bound C energy reservoir tailWork M n hC hE hR hwork)
    hsmall

/-- One additional dyadic separation multiplies the shell envelope by exactly
`1/4`. -/
theorem one_more_dyadic_lag_is_quarter (M : Nat) :
    (1 / 4 : ℝ) ^ (M + 1) = (1 / 4 : ℝ) * (1 / 4 : ℝ) ^ M := by
  rw [pow_succ]
  ring

#print axioms quarterPrefix_formula
#print axioms quarterPrefix_le_four_thirds
#print axioms quarterTail_le
#print axioms remote_tail_work_bound
#print axioms remote_tail_strict_absorption
#print axioms one_more_dyadic_lag_is_quarter

end NSYuTypeIRemoteTail
