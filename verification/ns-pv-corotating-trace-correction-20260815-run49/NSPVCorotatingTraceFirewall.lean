import Mathlib

/-!
# Corotating trace versus raw trace firewall

Finite algebra only. This file formalizes a two-state rotation-phase countermodel:
a gauge-corrected trace can be literally constant while raw traces differ, and a
rotation-invariant quadratic shell observable can remain unchanged.

It does not formalize logarithms, SO(3), Pineau--Vicol, RSS blow-downs,
Navier--Stokes, or any Millennium statement.
-/

namespace NSPVCorotatingTraceFirewall

abbrev Vec2 := ℤ × ℤ

def quarterTurn (v : Vec2) : Vec2 := (-v.2, v.1)

def inverseQuarterTurn (v : Vec2) : Vec2 := (v.2, -v.1)

def normSq (v : Vec2) : ℤ := v.1 * v.1 + v.2 * v.2

def rawTrace : Bool → Vec2
  | false => (1, 0)
  | true => (0, 1)

def correctedTrace : Bool → Vec2
  | false => rawTrace false
  | true => inverseQuarterTurn (rawTrace true)

theorem quarterTurn_inverse (v : Vec2) :
    inverseQuarterTurn (quarterTurn v) = v := by
  rcases v with ⟨x, y⟩
  simp [quarterTurn, inverseQuarterTurn]

theorem corrected_traces_equal :
    correctedTrace false = correctedTrace true := by
  rfl

theorem raw_traces_differ :
    rawTrace false ≠ rawTrace true := by
  norm_num [rawTrace]

theorem corrected_uniqueness_does_not_force_raw_uniqueness :
    correctedTrace false = correctedTrace true ∧
      rawTrace false ≠ rawTrace true := by
  exact ⟨corrected_traces_equal, raw_traces_differ⟩

theorem raw_trace_norm_invariant (b : Bool) :
    normSq (rawTrace b) = 1 := by
  cases b <;> norm_num [rawTrace, normSq]

theorem phase_change_preserves_shell_quadratic :
    normSq (rawTrace false) = normSq (rawTrace true) := by
  rw [raw_trace_norm_invariant, raw_trace_norm_invariant]

#print axioms quarterTurn_inverse
#print axioms corrected_traces_equal
#print axioms raw_traces_differ
#print axioms corrected_uniqueness_does_not_force_raw_uniqueness
#print axioms raw_trace_norm_invariant
#print axioms phase_change_preserves_shell_quadratic

end NSPVCorotatingTraceFirewall
