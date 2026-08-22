import Mathlib

/-!
# BSD quotient-zero firewall: finite logical core

This file formalizes only the elementary inference error isolated in the audit
of Destrempes--Malinin Proposition 12, Step 6:

  vanishing after projection to a quotient does not imply vanishing before
  projection when the projection has nontrivial kernel.

It does not formalize elliptic curves, Galois cohomology, Selmer groups, Sha,
the source theorem, the arithmetic counterexample, or BSD.
-/

namespace MillenniumBraid
namespace BSDQuotientZeroFirewall

/-- The elementary coordinate shadow modeling projection modulo a nonzero
one-dimensional subspace. -/
def quotientShadow (v : ℚ × ℚ) : ℚ := v.2

/-- Projection-zero says exactly that the vector lies in the kernel. -/
theorem quotientShadow_zero_only_forces_kernel_membership
    (v : ℚ × ℚ) (h : quotientShadow v = 0) :
    v ∈ {w : ℚ × ℚ | w.2 = 0} := by
  simpa [quotientShadow] using h

/-- The quotient projection has a nonzero kernel element. -/
theorem quotient_zero_does_not_imply_vector_zero :
    ∃ v : ℚ × ℚ, quotientShadow v = 0 ∧ v ≠ 0 := by
  refine ⟨(1, 0), by simp [quotientShadow], ?_⟩
  norm_num

/-- Consequently the universal lifting inference used in the audited proof is
false even in dimension two over the rationals. -/
theorem not_forall_projection_zero_implies_vector_zero :
    ¬ (∀ v : ℚ × ℚ, quotientShadow v = 0 → v = 0) := by
  intro h
  obtain ⟨v, hvproj, hvne⟩ := quotient_zero_does_not_imply_vector_zero
  exact hvne (h v hvproj)

#print axioms quotientShadow_zero_only_forces_kernel_membership
#print axioms quotient_zero_does_not_imply_vector_zero
#print axioms not_forall_projection_zero_implies_vector_zero

end BSDQuotientZeroFirewall
end MillenniumBraid
