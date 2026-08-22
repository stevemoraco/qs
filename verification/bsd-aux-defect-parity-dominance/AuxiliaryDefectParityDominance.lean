import Mathlib

namespace Millennium.BSD

/--
Finite parity dominance: if an auxiliary divisible defect `d` is even and
`r + d` has the global parity bit `omega`, then the Mordell--Weil rank bit
already equals `omega`.

This is Presburger arithmetic only. It does not formalize elliptic curves,
Selmer groups, p-parity, root numbers, Sha, BSD, or analytic rank.
-/
theorem rankParity_eq_of_auxiliaryDefectEven
    (r d omega : ℕ)
    (haux : (r + d) % 2 = omega % 2)
    (hd : d % 2 = 0) :
    r % 2 = omega % 2 := by
  omega

/--
Finite parity dominance: if an auxiliary divisible defect `d` is odd and
`r + d` has the global parity bit `omega`, then the Mordell--Weil rank bit
already differs from `omega`.

For BSD applications, once `omega` is independently identified with analytic
rank parity via the functional equation, this mismatch attacks rank equality
before any binary-threshold/Sha branch selection is needed.
-/
theorem rankParity_ne_of_auxiliaryDefectOdd
    (r d omega : ℕ)
    (haux : (r + d) % 2 = omega % 2)
    (hd : d % 2 = 1) :
    r % 2 ≠ omega % 2 := by
  omega

/-- The auxiliary defect parity completely determines whether the rank bit
matches the common global parity bit. -/
theorem rankParity_eq_iff_auxiliaryDefectEven
    (r d omega : ℕ)
    (haux : (r + d) % 2 = omega % 2) :
    (r % 2 = omega % 2) ↔ d % 2 = 0 := by
  omega

#print axioms rankParity_eq_of_auxiliaryDefectEven
#print axioms rankParity_ne_of_auxiliaryDefectOdd
#print axioms rankParity_eq_iff_auxiliaryDefectEven

end Millennium.BSD
