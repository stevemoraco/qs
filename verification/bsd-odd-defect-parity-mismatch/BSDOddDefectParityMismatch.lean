import Mathlib

/-!
Finite arithmetic shadow of the BSD odd-defect parity-mismatch certificate.

This file does NOT formalize elliptic curves, Selmer groups, Tate–Shafarevich groups,
p-parity, Kummer theory, or BSD. Those are explicit mathematical hypotheses outside
this finite theorem.
-/

namespace BSDOddDefectParityMismatch

/--
If a defect `eps` is known a priori to be `0` or `1`, the Selmer corank satisfies
`R = r + eps`, and Selmer parity is `omega`, then the odd defect occurs exactly
when Mordell–Weil parity differs from `omega`.
-/
theorem eps_eq_one_iff_parity_mismatch
    (r R omega eps : ℕ)
    (heps : eps = 0 ∨ eps = 1)
    (hKummer : R = r + eps)
    (hParity : R % 2 = omega % 2) :
    eps = 1 ↔ r % 2 ≠ omega % 2 := by
  rcases heps with rfl | rfl
  · simp_all
  · constructor
    · intro _
      omega
    · intro _
      rfl

/-- Equal Mordell–Weil/root parity forces the even defect in the binary regime. -/
theorem parity_match_forces_eps_zero
    (r R omega eps : ℕ)
    (heps : eps = 0 ∨ eps = 1)
    (hKummer : R = r + eps)
    (hParity : R % 2 = omega % 2)
    (hMatch : r % 2 = omega % 2) :
    eps = 0 := by
  rcases heps with rfl | rfl
  · rfl
  · omega

/-- A parity mismatch forces the odd defect in the binary regime. -/
theorem parity_mismatch_forces_eps_one
    (r R omega eps : ℕ)
    (heps : eps = 0 ∨ eps = 1)
    (hKummer : R = r + eps)
    (hParity : R % 2 = omega % 2)
    (hMismatch : r % 2 ≠ omega % 2) :
    eps = 1 := by
  rcases heps with rfl | rfl
  · simp_all
  · rfl

#print axioms eps_eq_one_iff_parity_mismatch
#print axioms parity_match_forces_eps_zero
#print axioms parity_mismatch_forces_eps_one

end BSDOddDefectParityMismatch
