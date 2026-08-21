import Mathlib

namespace Hodge
namespace C485MarkedSelfSquareFinite

structure MarkerExpansion (A V : Type*) where
  plain : A
  rightMarker : V
  leftMarker : V
  doubleMarker : ℚ

def markedExpansion {A V : Type*} (selfTerm : A) (v : V) :
    MarkerExpansion A V where
  plain := selfTerm
  rightMarker := v
  leftMarker := v
  doubleMarker := 1

@[simp] theorem markedExpansion_right
    {A V : Type*} (selfTerm : A) (v : V) :
    (markedExpansion selfTerm v).rightMarker = v := rfl

@[simp] theorem markedExpansion_left
    {A V : Type*} (selfTerm : A) (v : V) :
    (markedExpansion selfTerm v).leftMarker = v := rfl

@[simp] theorem markedExpansion_double
    {A V : Type*} (selfTerm : A) (v : V) :
    (markedExpansion selfTerm v).doubleMarker = 1 := rfl

theorem marked_algebraic_implies_extracted
    {A V : Type*}
    (sourceAlgebraic : MarkerExpansion A V → Prop)
    (targetAlgebraic : V → Prop)
    (hproject : ∀ z, sourceAlgebraic z → targetAlgebraic z.rightMarker)
    (selfTerm : A) (v : V)
    (hmarked : sourceAlgebraic (markedExpansion selfTerm v)) :
    targetAlgebraic v := by
  simpa using hproject (markedExpansion selfTerm v) hmarked

theorem recover_from_nonzero_rational_multiple
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (cycles : Submodule ℚ V)
    {d : ℚ} (hd : d ≠ 0) {v : V}
    (h : d • v ∈ cycles) :
    v ∈ cycles := by
  have hinv := cycles.smul_mem d⁻¹ h
  simpa [smul_smul, hd] using hinv

theorem codimension_ledger (n p : ℕ) :
    2 * p + p + n = p + (p + n + p) := by omega

theorem fiber_dimension_ledger (n p : ℕ) :
    p + n + p = n + 2 * p := by omega

theorem multiplied_codimension_ledger (n p : ℕ) :
    2 * p + p + n = n + 3 * p := by omega

#print axioms marked_algebraic_implies_extracted
#print axioms recover_from_nonzero_rational_multiple
#print axioms codimension_ledger
#print axioms fiber_dimension_ledger
#print axioms multiplied_codimension_ledger

end C485MarkedSelfSquareFinite
end Hodge
