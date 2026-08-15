import Mathlib

/-!
# Finite Mellin / Hardy-bracket absorption core

This file formalizes only scalar consequences of an abstract identity

`L / 4 + H = B`

and the exact rational scaling shadow of a separately certified Gaussian
Schwartz countermodel in the surrounding human audit.

It does **not** formalize Pineau--Vicol, weighted Hardy integration by parts,
the Gaussian integral calculation, vorticity, Navier--Stokes, regularity,
blow-up, or a Clay statement.
-/

namespace NSPVMellinHardyBracket

/-- If the bracket work exceeds the Hardy remainder by at most `eps`, then the
trace coefficient is at most `4 eps`. -/
theorem trace_bound_of_approx_hardy_dominance
    {L H B eps : ℝ}
    (hid : L / 4 + H = B)
    (hdom : B ≤ H + eps) :
    L ≤ 4 * eps := by
  linarith

/-- Exact Hardy domination kills a nonnegative trace coefficient. -/
theorem zero_trace_of_hardy_dominance
    {L H B : ℝ}
    (hL : 0 ≤ L)
    (hid : L / 4 + H = B)
    (hdom : B ≤ H) :
    L = 0 := by
  linarith

/-- A strict Hardy margin kills both the trace coefficient and the Hardy
remainder, hence also the bracket work. -/
theorem strict_hardy_margin_kills_all
    {L H B eta : ℝ}
    (hL : 0 ≤ L)
    (hH : 0 ≤ H)
    (heta : 0 < eta)
    (hid : L / 4 + H = B)
    (hdom : B ≤ (1 - eta) * H) :
    L = 0 ∧ H = 0 ∧ B = 0 := by
  have hprod : 0 ≤ eta * H := mul_nonneg (le_of_lt heta) hH
  have hL0 : L = 0 := by
    linarith
  have hprod0 : eta * H = 0 := by
    linarith
  have heta0 : eta ≠ 0 := ne_of_gt heta
  have hH0 : H = 0 := (mul_eq_zero.mp hprod0).resolve_left heta0
  have hB0 : B = 0 := by
    rw [← hid, hL0, hH0]
    norm_num
  exact ⟨hL0, hH0, hB0⟩

/-- The identity and nonnegativity alone do not force a zero trace: there is an
exact positive-trace scalar model. -/
theorem identity_alone_does_not_force_zero :
    ∃ L H B : ℝ, 0 < L ∧ 0 ≤ H ∧ L / 4 + H = B := by
  refine ⟨4, 0, 1, ?_, ?_, ?_⟩ <;> norm_num

/-- Rational shadow of the exact Gaussian certificate.

The surrounding symbolic calculation gives the common-`pi` normalized values
`H0 = 5147/35` and `B0 = 9154/8505`.  Once the amplitude exceeds the exact
ratio `H0/B0 = 1250721/9154`, cubic bracket scaling outruns quadratic Hardy
scaling. -/
theorem gaussian_normalized_scaling_breaks_unit_dominance
    {c : ℝ}
    (hc : (1250721 : ℝ) / 9154 < c) :
    c ^ 2 * ((5147 : ℝ) / 35) <
      c ^ 3 * ((9154 : ℝ) / 8505) := by
  have hcpos : 0 < c := by
    have ht : (0 : ℝ) < (1250721 : ℝ) / 9154 := by norm_num
    linarith
  have hbpos : (0 : ℝ) < (9154 : ℝ) / 8505 := by norm_num
  have hid :
      ((1250721 : ℝ) / 9154) * ((9154 : ℝ) / 8505) =
        (5147 : ℝ) / 35 := by
    norm_num
  have hbase :
      (5147 : ℝ) / 35 < c * ((9154 : ℝ) / 8505) := by
    rw [← hid]
    exact mul_lt_mul_of_pos_right hc hbpos
  have hc2pos : 0 < c ^ 2 := sq_pos_of_pos hcpos
  calc
    c ^ 2 * ((5147 : ℝ) / 35) <
        c ^ 2 * (c * ((9154 : ℝ) / 8505)) :=
      mul_lt_mul_of_pos_left hbase hc2pos
    _ = c ^ 3 * ((9154 : ℝ) / 8505) := by ring

#print axioms trace_bound_of_approx_hardy_dominance
#print axioms zero_trace_of_hardy_dominance
#print axioms strict_hardy_margin_kills_all
#print axioms identity_alone_does_not_force_zero
#print axioms gaussian_normalized_scaling_breaks_unit_dominance

end NSPVMellinHardyBracket
