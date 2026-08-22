import Mathlib

namespace PNPLeeGlobalConfigurationFirewall

/-- An `m`-cell binary tape region has `2^m` simultaneous global contents,
even when the head schedule is fixed independently of those contents. -/
theorem binary_global_configuration_count (m : ℕ) :
    Fintype.card (Fin m → Bool) = 2 ^ m := by
  simp

/-- Head-coordinate agreement does not imply equality of tape contents: already
with one binary cell there are two distinct global assignments. -/
theorem aligned_head_distinct_tapes :
    ∃ x y : Fin 1 → Bool, x ≠ y := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  intro h
  have := congrFun h ⟨0, by decide⟩
  simp at this

#print axioms binary_global_configuration_count
#print axioms aligned_head_distinct_tapes

end PNPLeeGlobalConfigurationFirewall
