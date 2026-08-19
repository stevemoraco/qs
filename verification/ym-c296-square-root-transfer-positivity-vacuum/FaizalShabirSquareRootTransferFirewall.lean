import Mathlib

/-!
# Faizal–Shabir square-root transfer positivity/vacuum firewalls

Finite real-algebra shadows of two transfer-operator typing issues.

1. A symmetric entrywise-nonnegative two-state kernel need not be positive
   semidefinite as an operator.
2. A symmetric matrix with strictly positive entries need not have the constant
   vector as an eigenvector; spectral-radius normalization alone therefore does
   not identify the constant function as the transfer vacuum.

This file does not formalize integral kernels, reflection positivity, Perron
operators, OS Hilbert spaces, Yang--Mills fields, or a mass gap.
-/

namespace Millennium.YangMills.FaizalShabirSquareRootTransferFirewall

/-- The symmetric entrywise-nonnegative matrix `[[0,1],[1,0]]` has negative
quadratic form on `(1,-1)`. -/
theorem entrywise_nonnegative_symmetric_not_psd :
    (0 : ℝ) * 1 ^ 2 + 2 * 1 * 1 * (-1) + 0 * (-1) ^ 2 < 0 := by
  norm_num

/-- The constant vector `(1,1)` is not an eigenvector of the symmetric
positive-entry matrix `[[2,1],[1,1]]`, because its two output coordinates are
`3` and `2`. -/
theorem positive_entry_symmetric_constant_not_eigenvector :
    ¬ ∃ r : ℝ, (3 : ℝ) = r ∧ (2 : ℝ) = r := by
  norm_num

#print axioms entrywise_nonnegative_symmetric_not_psd
#print axioms positive_entry_symmetric_constant_not_eigenvector

end Millennium.YangMills.FaizalShabirSquareRootTransferFirewall
