import Mathlib

/-!
# Pineau--Vicol Type-I mass-floor finite algebra

Finite real inequalities only.  This file does **not** formalize Pineau--Vicol,
vorticity, self-similar variables, measure theory, Navier--Stokes, or a Clay
statement.

The intended analytic use is the following scalar shadow.  If a Type-I
singularity forces a late-time L2 vorticity lower bound `theta/2`, while a
pointwise bound gives `|Omega| <= 2 K`, then splitting a fixed ball into
`|Omega| <= kappa` and `|Omega| > kappa`, with the low region contributing at
most `theta^2/8`, forces a positive measure `q` of the high region.
-/

namespace NSPineauVicolMassFloor

/-- If the total square mass is above `theta^2/4`, while the low-amplitude part
costs at most `theta^2/8` and the high-amplitude part costs at most
`4 K^2 q`, then the high-region mass must pay the displayed strict floor. -/
theorem superlevel_mass_floor
    (theta K E q : ℝ)
    (hLower : theta ^ 2 / 4 < E)
    (hUpper : E ≤ theta ^ 2 / 8 + 4 * K ^ 2 * q) :
    theta ^ 2 < 32 * K ^ 2 * q := by
  nlinarith

/-- A positive L2 floor and finite positive pointwise envelope force a genuinely
positive high-amplitude mass in the scalar budget. -/
theorem superlevel_mass_positive
    (theta K E q : ℝ)
    (htheta : 0 < theta)
    (hK : 0 < K)
    (hLower : theta ^ 2 / 4 < E)
    (hUpper : E ≤ theta ^ 2 / 8 + 4 * K ^ 2 * q) :
    0 < q := by
  have hFloor : theta ^ 2 < 32 * K ^ 2 * q :=
    superlevel_mass_floor theta K E q hLower hUpper
  have hthetaSq : 0 < theta ^ 2 := sq_pos_of_pos htheta
  have hKSq : 0 < K ^ 2 := sq_pos_of_pos hK
  nlinarith

/-- If total high-amplitude mass is covered by at most `N` equal upper cell
budgets, some admissible cell budget cannot lie below `mass/N`.  This is only
the scalar endpoint of a future finite-cover argument; no geometric cover is
constructed here. -/
theorem finite_cover_cell_floor
    (mass N cell : ℝ)
    (hN : 0 < N)
    (hcover : mass ≤ N * cell) :
    mass / N ≤ cell := by
  exact (div_le_iff₀ hN).2 hcover

/-- Combining a positive total mass with a finite positive cover count forces a
positive cell budget. -/
theorem finite_cover_cell_positive
    (mass N cell : ℝ)
    (hmass : 0 < mass)
    (hN : 0 < N)
    (hcover : mass ≤ N * cell) :
    0 < cell := by
  have hfloor : mass / N ≤ cell := finite_cover_cell_floor mass N cell hN hcover
  have hratio : 0 < mass / N := div_pos hmass hN
  linarith

#print axioms superlevel_mass_floor
#print axioms superlevel_mass_positive
#print axioms finite_cover_cell_floor
#print axioms finite_cover_cell_positive

end NSPineauVicolMassFloor
