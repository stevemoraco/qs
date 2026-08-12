import Mathlib

namespace BSDIdeleBlindnessFinite

variable {ι U V W : Type*}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]

/-- A shift in the common kernel of every local coordinate leaves the complete
    family of local coordinates unchanged. -/
theorem commonKernel_shift_local_same
    (locals : ι → U →+ V)
    (x k : U)
    (hlocal : ∀ i, locals i k = 0) :
    ∀ i, locals i (x + k) = locals i x := by
  intro i
  simp [map_add, hlocal i]

/-- An Archimedean coordinate that is nonzero on the common-kernel shift really
    distinguishes the shifted object. -/
theorem arch_shift_changes
    (arch : U →+ W)
    (x k : U)
    (harch : arch k ≠ 0) :
    arch (x + k) ≠ arch x := by
  intro hsame
  have hsum : arch x + arch k = arch x := by
    simpa [map_add] using hsame
  have hsum' : arch x + arch k = arch x + 0 := by
    simpa using hsum
  have hkzero : arch k = 0 := add_left_cancel hsum'
  exact harch hkzero

/-- The two conclusions combine to give the abstract local-to-Archimedean
    nonseparation firewall. -/
theorem local_same_arch_different
    (locals : ι → U →+ V)
    (arch : U →+ W)
    (x k : U)
    (hlocal : ∀ i, locals i k = 0)
    (harch : arch k ≠ 0) :
    (∀ i, locals i (x + k) = locals i x) ∧
      arch (x + k) ≠ arch x := by
  constructor
  · exact commonKernel_shift_local_same locals x k hlocal
  · exact arch_shift_changes arch x k harch

/-- A nonzero common kernel element proves that the complete family of local
    maps is not injective. -/
theorem local_family_not_injective
    (locals : ι → U →+ V)
    (k : U)
    (hk : k ≠ 0)
    (hlocal : ∀ i, locals i k = 0) :
    ¬ Function.Injective (fun x i => locals i x) := by
  intro hinj
  have hfun : (fun i => locals i k) = (fun i => locals i 0) := by
    funext i
    simp [hlocal i]
  have hkzero : k = 0 := hinj hfun
  exact hk hkzero

/-- In additive coordinates, the Archimedean change caused by the invisible
    shift is exactly the Archimedean value of that shift. -/
theorem arch_shift_difference
    (arch : U →+ W)
    (x k : U) :
    arch (x + k) - arch x = arch k := by
  simp [map_add]

#print axioms commonKernel_shift_local_same
#print axioms arch_shift_changes
#print axioms local_same_arch_different
#print axioms local_family_not_injective
#print axioms arch_shift_difference

end BSDIdeleBlindnessFinite
