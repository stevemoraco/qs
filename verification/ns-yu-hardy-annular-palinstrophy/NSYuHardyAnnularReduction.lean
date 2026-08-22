import Mathlib

/-!
# Navier--Stokes / Yu annular Hardy reduction: finite firewall

Finite algebra only.  This file does **not** formalize Runlong Yu's PDE theorem,
Hardy's inequality on R^3, filtered vorticity, suitable weak solutions, or a
Navier--Stokes regularity/blow-up theorem.

Primary-source motivation:

* Runlong Yu, arXiv:2606.27560v1 (25 Jun 2026), Definition 8.5 and
  Proposition 8.6.  For dyadic radii `r_k = 2^{-(k-j)} r_j`, the reassigned
  annular square reservoir contains weights

      2^{-(k-j)} * r_j^{-1} * annular_mass.

  The first theorem below records the exact scalar identity turning this into

      r_k * r_j^{-2} * annular_mass,

  i.e. the discrete coefficient corresponding to a Hardy weight.

* The absorption theorems expose the exact additional bridge needed after a
  spatial Hardy estimate: exterior filtered palinstrophy must itself be charged
  to the core dissipative budget with a strict coefficient margin.

* The final two lemmas record a mesoscopic split used in the human PDE audit:
  if the core radius is `r = s^3` and one cuts the exterior at radius `s`, then
  the raw coefficient `r / s^2` is exactly the small factor `s`.

These are reusable arithmetic interfaces, not PDE claims.
-/

namespace NSYuHardyAnnularReduction

/-- If `r_k = lag * r_j`, the Yu reassignment coefficient `lag / r_j`
    is exactly the Hardy-shaped coefficient `r_k / r_j^2`. -/
theorem shell_weight_is_hardy_weight
    {r_k r_j lag mass : ℝ}
    (hrj : r_j ≠ 0)
    (hscale : r_k = lag * r_j) :
    lag * (mass / r_j) = r_k * (mass / r_j ^ 2) := by
  rw [hscale]
  field_simp [hrj]

/-- Scalar endgame for a prospective exterior-Hardy repair.

If the far-field work is already reduced to `eta * Dcore + K * A2`,
if the quadratic annular reservoir satisfies `A2 <= H * Dext`, and if the
exterior dissipation is itself controlled by `theta * Dcore`, then the total
coefficient is exactly `eta + K*H*theta`.
-/
theorem hardy_exterior_absorption
    {mu eta Dcore K A2 H Dext theta : ℝ}
    (hK : 0 ≤ K)
    (hH : 0 ≤ H)
    (hmu : mu ≤ eta * Dcore + K * A2)
    (hA2 : A2 ≤ H * Dext)
    (hDext : Dext ≤ theta * Dcore) :
    mu ≤ (eta + K * H * theta) * Dcore := by
  have h1 : K * A2 ≤ K * (H * Dext) :=
    mul_le_mul_of_nonneg_left hA2 hK
  have hKH : 0 ≤ K * H := mul_nonneg hK hH
  have h2 : (K * H) * Dext ≤ (K * H) * (theta * Dcore) :=
    mul_le_mul_of_nonneg_left hDext hKH
  calc
    mu ≤ eta * Dcore + K * A2 := hmu
    _ ≤ eta * Dcore + K * (H * Dext) := by nlinarith [h1]
    _ = eta * Dcore + (K * H) * Dext := by ring
    _ ≤ eta * Dcore + (K * H) * (theta * Dcore) := by nlinarith [h2]
    _ = (eta + K * H * theta) * Dcore := by ring

/-- A strict total coefficient margin gives strict absorption. -/
theorem hardy_exterior_strict_margin
    {mu eta Dcore K A2 H Dext theta : ℝ}
    (hK : 0 ≤ K)
    (hH : 0 ≤ H)
    (hDcore : 0 < Dcore)
    (hmu : mu ≤ eta * Dcore + K * A2)
    (hA2 : A2 ≤ H * Dext)
    (hDext : Dext ≤ theta * Dcore)
    (hmargin : eta + K * H * theta < 1) :
    mu < Dcore := by
  have hbound : mu ≤ (eta + K * H * theta) * Dcore :=
    hardy_exterior_absorption hK hH hmu hA2 hDext
  nlinarith

/-- Core diffusion alone cannot control an independent positive exterior
    reservoir with any universal scalar constant.  A PDE bridge from exterior
    to core is logically indispensable. -/
theorem no_universal_core_only_control :
    ¬ (∃ C : ℝ, ∀ A2 Dcore : ℝ,
        0 ≤ A2 → 0 ≤ Dcore → A2 ≤ C * Dcore) := by
  rintro ⟨C, hC⟩
  have hbad := hC 1 0 (by norm_num) (by norm_num)
  norm_num at hbad

/-- Cubic mesoscopic split: choosing physical cutoff radius `rho=s` at core
    radius `r=s^3` leaves exactly the small factor `r/rho^2=s`. -/
theorem cubic_mesoscopic_split_factor
    {s : ℝ} (hs : s ≠ 0) :
    s ^ 3 / s ^ 2 = s := by
  field_simp [hs]

/-- Once the PDE estimate has reduced a far-tail reservoir to `C*s*E`, a
    uniform upper budget `E <= M` preserves the small factor `s`. -/
theorem mesoscopic_tail_charge
    {tail C s E M : ℝ}
    (hC : 0 ≤ C)
    (hs : 0 ≤ s)
    (hEM : E ≤ M)
    (htail : tail ≤ C * s * E) :
    tail ≤ C * M * s := by
  have hCs : 0 ≤ C * s := mul_nonneg hC hs
  have h := mul_le_mul_of_nonneg_left hEM hCs
  nlinarith

#print axioms shell_weight_is_hardy_weight
#print axioms hardy_exterior_absorption
#print axioms hardy_exterior_strict_margin
#print axioms no_universal_core_only_control
#print axioms cubic_mesoscopic_split_factor
#print axioms mesoscopic_tail_charge

end NSYuHardyAnnularReduction
