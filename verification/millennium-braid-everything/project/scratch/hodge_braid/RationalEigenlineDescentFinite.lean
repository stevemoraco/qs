import Mathlib

namespace HodgeBraid

variable {V : Type*} [AddCommGroup V]

/-- If two subspaces have trivial intersection, a vector lying in both must
vanish.  This is the finite core of the rational/nonreal-eigenline descent
obstruction. -/
theorem mem_distinct_lines_forces_zero
    [Field ℂ] [Module ℂ V]
    (L M : Submodule ℂ V)
    (hdisjoint : L ⊓ M = ⊥)
    (w : V) (hwL : w ∈ L) (hwM : w ∈ M) :
    w = 0 := by
  have hw : w ∈ L ⊓ M := ⟨hwL, hwM⟩
  rw [hdisjoint] at hw
  simpa using hw

/-- A fixed vector whose involution moves one eigenline into a disjoint
conjugate eigenline belongs to both lines. -/
theorem fixed_conjugate_vector_in_both
    {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (conj : W → W)
    (L M : Submodule K W)
    (hmap : ∀ w, w ∈ L → conj w ∈ M)
    (w : W) (hwL : w ∈ L) (hfix : conj w = w) :
    w ∈ M := by
  simpa [hfix] using hmap w hwL

end HodgeBraid
