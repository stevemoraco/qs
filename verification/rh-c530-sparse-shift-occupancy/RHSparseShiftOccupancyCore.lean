import Mathlib

/-!
# RH C530 finite sparse shifted-occupancy core

Finite real algebra only.  This file formalizes the load-bearing geometric
threshold-bracketing inequality and a sharp one-atom witness used in RH C530.

It does not formalize primes, the weighted moment `M(x)`, logarithmic layer
cake, Suzuki/Landau, BGST, zeta zeros, or RH.
-/

namespace Millennium
namespace RH
namespace C530

/-- Strict scalar shifted occupancy for a one-atom depth. -/
noncomputable def strictOcc (depth threshold : ℝ) : ℝ :=
  if threshold < depth then 1 else 0

/-- If a query `lam` lies below the next geometric threshold `hi = r*lo`, and
its occupancy is at most the occupancy at the lower threshold `lo`, then its
weighted occupancy is at most `r` times the lower-threshold weighted
occupancy.  This is the finite scalar core of `Q_m ≤ r_m G_m`. -/
theorem geometric_shift_bracket
    {lo lam hi r muLo muLam : ℝ}
    (hlo : 0 < lo)
    (hr : 0 ≤ r)
    (hgeom : hi = r * lo)
    (hlamhi : lam ≤ hi)
    (hmu : 0 ≤ muLam)
    (hmono : muLam ≤ muLo) :
    lam * muLam ≤ r * (lo * muLo) := by
  have hlo0 : 0 ≤ lo := le_of_lt hlo
  have hhi0 : 0 ≤ hi := by
    rw [hgeom]
    exact mul_nonneg hr hlo0
  have h1 : lam * muLam ≤ hi * muLam :=
    mul_le_mul_of_nonneg_right hlamhi hmu
  have h2 : hi * muLam ≤ hi * muLo :=
    mul_le_mul_of_nonneg_left hmono hhi0
  calc
    lam * muLam ≤ hi * muLam := h1
    _ ≤ hi * muLo := h2
    _ = r * (lo * muLo) := by rw [hgeom]; ring

/-- The one-atom strict occupancy is one at every lower threshold. -/
theorem strictOcc_lower_one {r : ℝ} (hr : 1 < r) :
    strictOcc r 1 = 1 := by
  simp [strictOcc, hr]

/-- The same atom is absent at the upper threshold because the shifted index
uses the strict event `depth > threshold`. -/
theorem strictOcc_at_depth_zero (r : ℝ) :
    strictOcc r r = 0 := by
  simp [strictOcc]

/-- A single atom at depth `r>1` attains the full geometric spacing loss:
the lower-threshold menu value is one while the weak left-limit value is `r`.
Thus the factor in `geometric_shift_bracket` is sharp source-blindly. -/
theorem oneAtom_geometric_loss_sharp {r : ℝ} (hr : 1 < r) :
    r = r * (1 * strictOcc r 1) := by
  rw [strictOcc_lower_one hr]
  ring

/-- For a fixed one-step menu, arbitrarily large geometric ratio gives an
arbitrarily large weak/menu distortion. -/
theorem fixedMenu_unbounded_loss
    {C : ℝ} (hC : 0 < C) :
    ∃ r : ℝ, 1 < r ∧ C < r ∧
      strictOcc r 1 = 1 ∧ strictOcc r r = 0 := by
  let r : ℝ := C + 2
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · dsimp [r]
    linarith
  · dsimp [r]
    linarith
  · exact strictOcc_lower_one (by dsimp [r]; linarith)
  · exact strictOcc_at_depth_zero r

#print axioms geometric_shift_bracket
#print axioms strictOcc_lower_one
#print axioms strictOcc_at_depth_zero
#print axioms oneAtom_geometric_loss_sharp
#print axioms fixedMenu_unbounded_loss

end C530
end RH
end Millennium
