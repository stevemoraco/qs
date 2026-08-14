import Mathlib

noncomputable section

/-!
# Navier--Stokes filtered-reservoir absorption gate

Finite scalar firewalls extracted from the audit of Runlong Yu,
`arXiv:2606.27560v1` (25 Jun 2026).

The paper's near-field estimate has the schematic form

`V <= (1-eps) P + B O`,

where `P` is filtered diffusion and `O` is the lower-order filtered-enstrophy
reservoir.  Its later defect surplus subtracts the `B O` term before taking a
positive part.  Consequently, vanishing of the post-near-field surplus is not,
by itself, decay of `O` or an endpoint contraction.

This file proves only finite algebra and critical countermodels.  It does not
formalize Yu's PDE theorem, Navier--Stokes regularity, or blowup.
-/

namespace NSYuReservoirAbsorptionGate

/-- Source-shaped toy positive surplus after subtracting a reservoir term. -/
def toySurplus (Eout P Ein B O : ℝ) : ℝ :=
  max (Eout + P - Ein - B * O) 0

/-- A flat nonzero reservoir is compatible with identically zero post-subtraction
surplus. -/
theorem flatReservoir_has_zero_surplus :
    toySurplus 1 0 1 1 1 = 0 := by
  norm_num [toySurplus]

/-- Therefore `surplus = 0` cannot logically imply `reservoir = 0`. -/
theorem surplusZero_does_not_force_reservoirZero :
    ¬ (∀ Eout P Ein B O : ℝ, toySurplus Eout P Ein B O = 0 → O = 0) := by
  intro h
  have hzero : (1 : ℝ) = 0 :=
    h 1 0 1 1 1 flatReservoir_has_zero_surplus
  norm_num at hzero

/-- Exact finite algebraic condition that turns the Yu-shaped near-field estimate
into strict diffusion absorption: the reservoir must itself be controlled by a
small enough multiple of diffusion. -/
theorem reservoirAbsorption_closes
    (V P O eps B kappa : ℝ)
    (hP : 0 < P)
    (hB : 0 ≤ B)
    (hV : V ≤ (1 - eps) * P + B * O)
    (hO : O ≤ kappa * P)
    (hgap : B * kappa < eps) :
    V < P := by
  have hBO : B * O ≤ B * (kappa * P) :=
    mul_le_mul_of_nonneg_left hO hB
  have hscaled : (B * kappa) * P < eps * P :=
    mul_lt_mul_of_pos_right hgap hP
  calc
    V ≤ (1 - eps) * P + B * O := hV
    _ ≤ (1 - eps) * P + B * (kappa * P) := by
      exact add_le_add_right hBO ((1 - eps) * P)
    _ < P := by
      nlinarith

/-- Endpoint version of the same gate.  If the entire reservoir payment consumes
only a strict fraction `theta < 1` of the retained diffusion margin, the output
endpoint is strictly below the input endpoint. -/
theorem strictEndpointDrop_of_reservoirFraction
    (Eout Ein P eps B O theta : ℝ)
    (hP : 0 < P)
    (heps : 0 < eps)
    (htheta : theta < 1)
    (hbalance : Eout + eps * P ≤ Ein + B * O)
    (hreservoir : B * O ≤ theta * (eps * P)) :
    Eout < Ein := by
  have hmargin : 0 < eps * P := mul_pos heps hP
  have hstrict : theta * (eps * P) < 1 * (eps * P) :=
    mul_lt_mul_of_pos_right htheta hmargin
  nlinarith

/-! ## Yu filter-ratio penalty cannot be tuned small -/

/-- Elementary reparameterized lower bound.  If `a = 1/rho >= 4` and
`b = rho/sigma >= 1`, then the geometric factor `b^5 a^3` is at least `64`. -/
theorem reparameterizedFilterPenalty_lowerBound
    (a b : ℝ) (ha : 4 ≤ a) (hb : 1 ≤ b) :
    64 ≤ b ^ 5 * a ^ 3 := by
  have hbpow : (1 : ℝ) ^ 5 ≤ b ^ 5 := by
    gcongr
  have hapow : (4 : ℝ) ^ 3 ≤ a ^ 3 := by
    gcongr
  calc
    (64 : ℝ) = (1 : ℝ) ^ 5 * (4 : ℝ) ^ 3 := by norm_num
    _ ≤ b ^ 5 * a ^ 3 := by
      exact mul_le_mul hbpow hapow (by norm_num) (by positivity)

/-- On Yu's admissible parameter range `0 < sigma <= rho <= 1/4`, the bare
geometric reservoir factor `rho^2 * sigma^(-5)` is never small: its minimum is
at least `64`.  Thus shrinking the filter ratio cannot create the missing
reservoir absorption margin. -/
theorem admissibleFilterPenalty_lowerBound
    (rho sigma : ℝ)
    (hsigma : 0 < sigma)
    (hsr : sigma ≤ rho)
    (hrho : rho ≤ (1 : ℝ) / 4) :
    64 ≤ rho ^ 2 / sigma ^ 5 := by
  have hrhopos : 0 < rho := lt_of_lt_of_le hsigma hsr
  have ha : 4 ≤ (1 : ℝ) / rho := by
    apply (le_div_iff₀ hrhopos).2
    nlinarith
  have hb : 1 ≤ rho / sigma := by
    exact (le_div_iff₀ hsigma).2 (by simpa using hsr)
  have hbase := reparameterizedFilterPenalty_lowerBound (1 / rho) (rho / sigma) ha hb
  have hs0 : sigma ≠ 0 := ne_of_gt hsigma
  have hr0 : rho ≠ 0 := ne_of_gt hrhopos
  rw [show (rho / sigma) ^ 5 * (1 / rho) ^ 3 = rho ^ 2 / sigma ^ 5 by
    field_simp [hs0, hr0]] at hbase
  exact hbase

/-! ## Rigid-rotation null mode: full reservoir absorption cannot be universal -/

/-- For the affine rigid rotation `u=(-c*y,c*x,0)`, the symmetric off-diagonal
strain coefficient is zero. -/
theorem rigidRotation_symmetricStrain_zero (c : ℝ) :
    ((-c) + c) / 2 = 0 := by ring

/-- The same rigid rotation has constant vertical vorticity `2c`. -/
theorem rigidRotation_vorticityZ (c : ℝ) :
    c - (-c) = 2 * c := by ring

/-- Its finite stationary Navier--Stokes coefficient balance closes exactly with
pressure gradient `(c^2*x,c^2*y,0)`: the convective acceleration is the opposite
radial vector.  This is the algebraic core of the smooth rigid-rotation null
mode; no PDE differentiation is encoded here. -/
theorem rigidRotation_stationaryBalance (c x y : ℝ) :
    ((-c * y) * 0 + (c * x) * (-c) + c ^ 2 * x = 0) ∧
    ((-c * y) * c + (c * x) * 0 + c ^ 2 * y = 0) := by
  constructor <;> ring

/-- Nonzero rigid rotation therefore has positive constant-vorticity enstrophy
while the vorticity-gradient cost is zero.  A universal estimate of the form
`O <= kappa * P` cannot hold before quotienting/removing this coherent null mode. -/
theorem rigidRotation_positiveReservoir_zeroPalinstrophy
    (c kappa : ℝ) (hc : c ≠ 0) :
    0 < (2 * c) ^ 2 ∧ ¬ ((2 * c) ^ 2 ≤ kappa * 0) := by
  have h2c : 2 * c ≠ 0 := mul_ne_zero (by norm_num) hc
  have hpos : 0 < (2 * c) ^ 2 := sq_pos_of_ne_zero h2c
  exact ⟨hpos, by intro h; nlinarith⟩

/-! ## Critical finite-energy normalization firewall -/

def dyadicShellEnergy (k : ℕ) : ℝ := ((1 : ℝ) / 2) ^ k

def dyadicCriticalNormalizer (k : ℕ) : ℝ := (2 : ℝ) ^ k

/-- A critical shell may lose geometrically small *unnormalized* energy while its
scale-normalized amount remains exactly one at every depth. -/
theorem criticalNormalizedEnergy_plateau (k : ℕ) :
    dyadicCriticalNormalizer k * dyadicShellEnergy k = 1 := by
  calc
    dyadicCriticalNormalizer k * dyadicShellEnergy k =
        (2 : ℝ) ^ k * ((1 : ℝ) / 2) ^ k := by rfl
    _ = ((2 : ℝ) * ((1 : ℝ) / 2)) ^ k := by rw [mul_pow]
    _ = 1 := by norm_num

/-- Exact finite geometric energy budget. -/
theorem dyadicShellEnergy_sum (N : ℕ) :
    Finset.sum (Finset.range N) (fun k => dyadicShellEnergy k) =
      2 * (1 - ((1 : ℝ) / 2) ^ N) := by
  induction N with
  | zero => norm_num [dyadicShellEnergy]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [dyadicShellEnergy, pow_succ]
      ring

/-- Hence the total unnormalized budget stays finite. -/
theorem dyadicShellEnergy_uniform_budget (N : ℕ) :
    Finset.sum (Finset.range N) (fun k => dyadicShellEnergy k) ≤ 2 := by
  rw [dyadicShellEnergy_sum]
  have hpow : 0 ≤ ((1 : ℝ) / 2) ^ N := by positivity
  linarith

/-- Finite energy alone therefore does not force decay of a critical normalized
local coefficient: the same model has a uniformly finite raw budget and a flat
normalized value at every scale. -/
theorem finiteEnergy_does_not_force_criticalNormalizedDecay (N : ℕ) :
    Finset.sum (Finset.range N) (fun k => dyadicShellEnergy k) ≤ 2 ∧
    (∀ k : ℕ, dyadicCriticalNormalizer k * dyadicShellEnergy k = 1) := by
  exact ⟨dyadicShellEnergy_uniform_budget N, criticalNormalizedEnergy_plateau⟩

#print axioms flatReservoir_has_zero_surplus
#print axioms surplusZero_does_not_force_reservoirZero
#print axioms reservoirAbsorption_closes
#print axioms strictEndpointDrop_of_reservoirFraction
#print axioms reparameterizedFilterPenalty_lowerBound
#print axioms admissibleFilterPenalty_lowerBound
#print axioms rigidRotation_symmetricStrain_zero
#print axioms rigidRotation_vorticityZ
#print axioms rigidRotation_stationaryBalance
#print axioms rigidRotation_positiveReservoir_zeroPalinstrophy
#print axioms criticalNormalizedEnergy_plateau
#print axioms dyadicShellEnergy_sum
#print axioms dyadicShellEnergy_uniform_budget
#print axioms finiteEnergy_does_not_force_criticalNormalizedDecay

end NSYuReservoirAbsorptionGate
