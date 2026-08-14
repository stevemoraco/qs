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

This file proves only finite algebra and a critical dyadic countermodel.  It does
not formalize Yu's PDE theorem, Navier--Stokes solutions, regularity, or blowup.
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
      exact add_le_add_left hBO ((1 - eps) * P)
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
#print axioms criticalNormalizedEnergy_plateau
#print axioms dyadicShellEnergy_sum
#print axioms dyadicShellEnergy_uniform_budget
#print axioms finiteEnergy_does_not_force_criticalNormalizedDecay

end NSYuReservoirAbsorptionGate
