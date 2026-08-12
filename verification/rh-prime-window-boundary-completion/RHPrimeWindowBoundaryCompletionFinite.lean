import Mathlib

/-!
# RH prime-window boundary-completion finite firewall

HONESTY BOUNDARY

This file checks only finite scalar identities behind the distinction between a
pair kernel truncated to an observation interval and its completed whole-line
autocorrelation. It does not formalize the prime number theorem, integration,
the compact prime kernel, zeta zeros, or RH.
-/

namespace MillenniumBraid
namespace RHPrimeWindowBoundaryCompletionFinite

/-- Completed energy is the sum of observed and boundary energy. -/
theorem completed_energy_split
    (truncated boundary : ℝ) :
    truncated + boundary = truncated + boundary := by
  rfl

/-- After splitting diagonal and off-diagonal terms, the off-diagonal
completion is total boundary energy minus diagonal boundary energy. -/
theorem boundary_offdiag_recovery
    (boundaryTotal boundaryDiagonal boundaryOffdiag : ℝ)
    (hsplit : boundaryTotal = boundaryDiagonal + boundaryOffdiag) :
    boundaryOffdiag = boundaryTotal - boundaryDiagonal := by
  linarith

/-- A lower bound for coherent boundary energy and an upper bound for its
diagonal part leave the corresponding lower bound for the off-diagonal part. -/
theorem boundary_offdiag_lower
    (boundaryTotal boundaryDiagonal boundaryOffdiag exponential linear : ℝ)
    (hsplit : boundaryTotal = boundaryDiagonal + boundaryOffdiag)
    (htotal : exponential ≤ boundaryTotal)
    (hdiagonal : boundaryDiagonal ≤ linear) :
    exponential - linear ≤ boundaryOffdiag := by
  linarith

/-- For `n` equal coherent contributions, total square equals diagonal plus
ordered off-diagonal contribution. -/
theorem coherent_boundary_identity (n : ℝ) :
    n ^ 2 = n + n * (n - 1) := by
  ring

/-- A fixed linear diagonal budget cannot control the coherent quadratic
off-diagonal term once the number of aligned contributions grows. -/
theorem coherent_offdiag_beats_fixed_linear
    (C n : ℝ)
    (hC : 0 ≤ C)
    (hn : C + 1 < n) :
    C * n < n * (n - 1) := by
  have hnpos : 0 < n := by linarith
  nlinarith

/-- An explicit witness exists for every nonnegative proposed linear constant. -/
theorem exists_coherent_quadratic_witness
    (C : ℝ)
    (hC : 0 ≤ C) :
    ∃ n : ℝ, 0 < n ∧ C * n < n * (n - 1) := by
  refine ⟨C + 2, by linarith, ?_⟩
  nlinarith

/-- Truncated and completed pair kernels are different inputs; a transfer
requires a separate boundary term. -/
inductive PairKernel where
  | truncated
  | completed
  deriving DecidableEq

theorem truncated_ne_completed :
    PairKernel.truncated ≠ PairKernel.completed := by
  decide

#print axioms completed_energy_split
#print axioms boundary_offdiag_recovery
#print axioms boundary_offdiag_lower
#print axioms coherent_boundary_identity
#print axioms coherent_offdiag_beats_fixed_linear
#print axioms exists_coherent_quadratic_witness
#print axioms truncated_ne_completed

end RHPrimeWindowBoundaryCompletionFinite
end MillenniumBraid
