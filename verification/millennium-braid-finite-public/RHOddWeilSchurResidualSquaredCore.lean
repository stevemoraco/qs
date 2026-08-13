import Mathlib

/-!
# Residual-squared Schur-complement firewall

Finite scalar shadow of the exact Feshbach residual identity used by the
odd-Weil RH route.  This file does not define the Weil form, zeta, Yoshida's
theorem, Hilbert-space operators, or RH.
-/

namespace RHBraid
namespace OddWeilSchurResidual

/-- Exact scalar residual identity.  `A - B^2 / D` is the exact scalar Schur
complement; `A - 2*B*y + D*y^2` is its completed-square approximation; and
`D*y-B` is the tail-solve residual. -/
theorem residual_squared_identity
    (A B D y : ℝ) (hD : D ≠ 0) :
    A - B^2 / D =
      (A - 2 * B * y + D * y^2) - (D * y - B)^2 / D := by
  field_simp [hD]
  ring

/-- If the residual square is at most `D * δ * s`, then the exact Schur value
is no worse than the computable completed-square value by `δ*s`. -/
theorem schur_lower_bound_of_residual_budget
    (A B D y δ s : ℝ)
    (hD : 0 < D)
    (hres : (D * y - B)^2 ≤ D * (δ * s)) :
    (A - 2 * B * y + D * y^2) - δ * s ≤ A - B^2 / D := by
  have hpen : (D * y - B)^2 / D ≤ δ * s := by
    exact (div_le_iff₀ hD).2 (by simpa [mul_assoc] using hres)
  rw [residual_squared_identity A B D y (ne_of_gt hD)]
  linarith

/-- Approximate lower defect plus residual defect add linearly.  This is the
finite scalar bookkeeping used before the separate vanishing-defect theorem. -/
theorem schur_defect_addition
    (A B D y η δ s : ℝ)
    (hD : 0 < D)
    (hs : 0 ≤ s)
    (happrox : -(η * s) ≤ A - 2 * B * y + D * y^2)
    (hres : (D * y - B)^2 ≤ D * (δ * s)) :
    -((η + δ) * s) ≤ A - B^2 / D := by
  have hlower := schur_lower_bound_of_residual_budget A B D y δ s hD hres
  nlinarith

/-- Cofinal scalar package: if each exact Schur value admits approximate and
residual defects whose sum can be made arbitrarily small, then it is
nonnegative. -/
theorem nonneg_of_schur_residual_vanishing
    (q s : ℝ) (η δ : ℕ → ℝ)
    (hs : 0 ≤ s)
    (hbound : ∀ n, -((η n + δ n) * s) ≤ q)
    (hvanish : ∀ e : ℝ, 0 < e → ∃ n, η n + δ n < e) :
    0 ≤ q := by
  by_contra hq
  have hqneg : q < 0 := lt_of_not_ge hq
  by_cases hs0 : s = 0
  · have hnonneg : 0 ≤ q := by
      simpa [hs0] using hbound 0
    exact (not_lt_of_ge hnonneg) hqneg
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have hepsilon : 0 < (-q) / s := div_pos (neg_pos.mpr hqneg) hspos
    obtain ⟨n, hn⟩ := hvanish ((-q) / s) hepsilon
    have hscaled : (η n + δ n) * s < -q :=
      (lt_div_iff₀ hspos).mp hn
    have hbad : q < -((η n + δ n) * s) := by
      nlinarith
    exact (not_lt_of_ge (hbound n)) hbad

#print axioms residual_squared_identity
#print axioms schur_lower_bound_of_residual_budget
#print axioms schur_defect_addition
#print axioms nonneg_of_schur_residual_vanishing

end OddWeilSchurResidual
end RHBraid
