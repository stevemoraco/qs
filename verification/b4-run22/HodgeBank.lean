import Mathlib

namespace Millennium.Hodge.RationalScalarLattice

def PreservesIntegerLattice (q : ℚ) : Prop :=
  ∀ z : ℤ, ∃ w : ℤ, q * (z : ℚ) = (w : ℚ)

theorem banker_integral_scalar_preserves_integer_lattice
    (k : ℤ) : PreservesIntegerLattice (k : ℚ) := by
  intro z
  refine ⟨k * z, ?_⟩
  norm_num

theorem critic_half_scalar_does_not_preserve_integer_lattice :
    ¬ PreservesIntegerLattice (1 / 2 : ℚ) := by
  intro h
  obtain ⟨w, hw⟩ := h 1
  have hw' : (2 : ℚ) * (w : ℚ) = 1 := by
    norm_num at hw ⊢
    linarith
  have hw'' : 2 * w = 1 := by
    exact_mod_cast hw'
  omega

theorem cleaner_lattice_preservation_forces_integral_scalar
    (q : ℚ) (h : PreservesIntegerLattice q) :
    ∃ k : ℤ, q = (k : ℚ) := by
  obtain ⟨k, hk⟩ := h 1
  refine ⟨k, ?_⟩
  simpa using hk

#print axioms banker_integral_scalar_preserves_integer_lattice
#print axioms critic_half_scalar_does_not_preserve_integer_lattice
#print axioms cleaner_lattice_preservation_forces_integral_scalar

end Millennium.Hodge.RationalScalarLattice
