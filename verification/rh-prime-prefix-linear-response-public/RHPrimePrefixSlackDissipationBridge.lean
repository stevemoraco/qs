import Mathlib

namespace RHPrimePrefixSlackDissipationBridge

/--
The difference between half the weighted quadratic discrepancy energy and the
square-root AM-GM debt is an exact signed cubic boundary energy.

Here `r^2` is the endpoint, `s^2` is the corresponding Chebyshev value,
`W=(r^2-s^2)^2/(2r^3)`, and `G=(r-s)^2/r`.
-/
theorem boundary_cubic_factorization
    {r s W G : ℝ}
    (hr : r ≠ 0)
    (hW : W = (r ^ 2 - s ^ 2) ^ 2 / (2 * r ^ 3))
    (hG : G = (r - s) ^ 2 / r) :
    W / 2 - G =
      (s - r) ^ 3 * (s + 3 * r) / (4 * r ^ 3) := by
  rw [hW, hG]
  field_simp [hr]
  ring

/--
Abstract compatibility of the two exact decompositions of the same prefix
increment. If the increment is half the signed kick sum plus slack, while the
critical margin is half the same kick sum plus dissipation and boundary
energy, then accumulated slack is exactly dissipation plus the boundary-energy
change minus the AM-GM-debt change.
-/
theorem slack_dissipation_bridge
    {F F₀ M M₀ H I W W₀ G G₀ S : ℝ}
    (hPrefix : F - F₀ = H / 2 + S)
    (hLedger : M - M₀ = H / 2 + 3 * I / 8 + (W - W₀) / 2)
    (hDebt : G = M - F)
    (hDebt₀ : G₀ = M₀ - F₀) :
    S = 3 * I / 8 + (W - W₀) / 2 - (G - G₀) := by
  linarith

/--
After replacing `W/2-G` by the cubic boundary energy `B`, the accumulated
slack is exactly `3I/8 + B-B₀`.
-/
theorem slack_dissipation_cubic_boundary
    {F F₀ M M₀ H I W W₀ G G₀ S B B₀ : ℝ}
    (hPrefix : F - F₀ = H / 2 + S)
    (hLedger : M - M₀ = H / 2 + 3 * I / 8 + (W - W₀) / 2)
    (hDebt : G = M - F)
    (hDebt₀ : G₀ = M₀ - F₀)
    (hBoundary : W / 2 - G = B)
    (hBoundary₀ : W₀ / 2 - G₀ = B₀) :
    S = 3 * I / 8 + B - B₀ := by
  have hBridge := slack_dissipation_bridge
    hPrefix hLedger hDebt hDebt₀
  linarith

/--
Nonnegative accumulated Bregman slack forces the cubic boundary drop to be no
larger than the critical quadratic dissipation reserve.
-/
theorem cubic_boundary_drop_le_dissipation
    {I S B B₀ : ℝ}
    (hIdentity : S = 3 * I / 8 + B - B₀)
    (hSlack : 0 ≤ S) :
    B₀ - B ≤ 3 * I / 8 := by
  linarith

#print axioms boundary_cubic_factorization
#print axioms slack_dissipation_bridge
#print axioms slack_dissipation_cubic_boundary
#print axioms cubic_boundary_drop_le_dissipation

end RHPrimePrefixSlackDissipationBridge
