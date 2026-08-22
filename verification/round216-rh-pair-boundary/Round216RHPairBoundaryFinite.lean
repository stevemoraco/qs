import Mathlib

/-!
# Round 216 RH pair-boundary finite cores

This file formalizes only a two-tap geometric boundary model and the scalar
algebra behind the corrected interval-dependent off-diagonal estimate.

It does not formalize integrals, prime sums, the prime number theorem, zeta
zeros, Suzuki's Weil form, or the Riemann hypothesis.
-/

namespace Millennium
namespace Round216RH

/-- The two-tap filter annihilates a geometric sequence at every interior
index. -/
theorem geometric_filter_interior_cancels
    (r : ℝ) (n : ℕ) :
    r ^ (n + 1) - r * r ^ n = 0 := by
  rw [pow_succ]
  ring

/-- The first missing sample after truncating the geometric sequence is an
upper-boundary value of magnitude `r^(N+1)`. -/
def upperBoundarySample (r : ℝ) (N : ℕ) : ℝ :=
  -r * r ^ N

theorem upper_boundary_sample_exact
    (r : ℝ) (N : ℕ) :
    upperBoundarySample r N = -(r ^ (N + 1)) := by
  simp [upperBoundarySample, pow_succ, mul_comm]

/-- Its squared boundary energy is the square of the exponentially growing
sample, despite exact interior annihilation. -/
theorem upper_boundary_energy_exact
    (r : ℝ) (N : ℕ) :
    upperBoundarySample r N ^ 2 = (r ^ (N + 1)) ^ 2 := by
  rw [upper_boundary_sample_exact]
  ring

/-- Abstractly, zero interior energy places no bound on a discarded boundary
energy: the latter can exceed any prescribed nonnegative threshold. -/
theorem zero_interior_allows_arbitrarily_large_boundary
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ interior boundary full : ℝ,
      interior = 0 ∧
      full = interior + boundary ∧
      K < boundary := by
  refine ⟨0, K + 1, K + 1, rfl, ?_, ?_⟩
  · ring
  · linarith

/-- Correct scalar endpoint for the interval-dependent pair law.  If the
complete mean square is `O(T)` and the exact diagonal differs from `A*T^2` by
at most `B*T`, then the exact off-diagonal differs from `-A*T^2` by at most
`(B+C)*T`. -/
theorem exact_offdiagonal_from_total_and_diagonal
    (T total diagonal offDiagonal A B C : ℝ)
    (hT : 0 ≤ T)
    (hB : 0 ≤ B)
    (hC : 0 ≤ C)
    (htotal0 : 0 ≤ total)
    (htotal : total ≤ C * T)
    (hdiag : |diagonal - A * T ^ 2| ≤ B * T)
    (hdecomp : total = diagonal + offDiagonal) :
    |offDiagonal + A * T ^ 2| ≤ (B + C) * T := by
  have hdiagBounds :
      -(B * T) ≤ diagonal - A * T ^ 2 ∧
        diagonal - A * T ^ 2 ≤ B * T :=
    (abs_le.mp hdiag)
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hB hT, mul_nonneg hC hT]
  · nlinarith [mul_nonneg hB hT, mul_nonneg hC hT]

/-- A translation-invariant full-correlation quantity equals the interval
quantity plus the discarded boundary energy.  Positivity gives only a
one-sided comparison; it does not make the boundary small. -/
theorem full_correlation_decomposition
    (interior boundary full : ℝ)
    (hboundary : 0 ≤ boundary)
    (hfull : full = interior + boundary) :
    interior ≤ full := by
  linarith

#print axioms geometric_filter_interior_cancels
#print axioms upper_boundary_sample_exact
#print axioms upper_boundary_energy_exact
#print axioms zero_interior_allows_arbitrarily_large_boundary
#print axioms exact_offdiagonal_from_total_and_diagonal
#print axioms full_correlation_decomposition

end Round216RH
end Millennium
