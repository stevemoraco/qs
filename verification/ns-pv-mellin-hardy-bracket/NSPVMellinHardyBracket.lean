import Mathlib

/-!
# Finite Mellin / Hardy-bracket absorption core

This file formalizes only scalar consequences of an abstract identity

`L / 4 + H = B`

that arises in the surrounding human audit of a weighted vorticity Mellin
identity for rotated backwards self-similar Navier--Stokes profiles.

It does **not** formalize Pineau--Vicol, weighted Hardy integration by parts,
vorticity, Navier--Stokes, regularity, blow-up, or a Clay statement.
-/

namespace NSPVMellinHardyBracket

/-- If the bracket work exceeds the nonnegative Hardy remainder by at most
`eps`, then the nonnegative trace coefficient is at most `4 eps`. -/
theorem trace_bound_of_approx_hardy_dominance
    {L H B eps : ℝ}
    (hL : 0 ≤ L)
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

#print axioms trace_bound_of_approx_hardy_dominance
#print axioms zero_trace_of_hardy_dominance
#print axioms strict_hardy_margin_kills_all
#print axioms identity_alone_does_not_force_zero

end NSPVMellinHardyBracket
