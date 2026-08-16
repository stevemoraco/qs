import Mathlib

/-!
# Pineau--Vicol weighted resonance sign firewall

Finite real-algebra companion to the weighted RSS audit.  This file does **not**
formalize weighted function spaces, adjoint kernels, the RSS PDE, Pineau--Vicol,
Navier--Stokes regularity or blow-up, or any Clay theorem.

The source-level consumer has the schematic exact resonance

  `(2 * alpha * C)^2 = N^2`

and Cauchy--Schwarz

  `C^2 <= N * S`,

with `N > 0`.  The finite theorem below records the load-bearing sign: these
hypotheses force `N <= 4 * alpha^2 * S`, so the scaled candidate gap
`N - 4 * alpha^2 * S` is nonpositive.  Exact resonance is also compatible with
a strictly negative scaled gap, so excluding equality cannot by itself produce
a positive margin.
-/

namespace NSPVWeightedResonanceSignFirewall

theorem resonance_cauchy_forces_scaled_shear
    {alpha N S C : ℝ}
    (hN : 0 < N)
    (hres : (2 * alpha * C) ^ 2 = N ^ 2)
    (hcs : C ^ 2 ≤ N * S) :
    N ≤ 4 * alpha ^ 2 * S := by
  have hmul :
      (2 * alpha) ^ 2 * C ^ 2 ≤ (2 * alpha) ^ 2 * (N * S) :=
    mul_le_mul_of_nonneg_left hcs (sq_nonneg (2 * alpha))
  have hsq : N ^ 2 ≤ (2 * alpha) ^ 2 * (N * S) := by
    calc
      N ^ 2 = (2 * alpha * C) ^ 2 := hres.symm
      _ = (2 * alpha) ^ 2 * C ^ 2 := by ring
      _ ≤ (2 * alpha) ^ 2 * (N * S) := hmul
  have hfactor : N * N ≤ N * (4 * alpha ^ 2 * S) := by
    calc
      N * N = N ^ 2 := by ring
      _ ≤ (2 * alpha) ^ 2 * (N * S) := hsq
      _ = N * (4 * alpha ^ 2 * S) := by ring
  exact le_of_mul_le_mul_left hfactor hN

theorem scaled_resonance_gap_nonpositive
    {alpha N S C : ℝ}
    (hN : 0 < N)
    (hres : (2 * alpha * C) ^ 2 = N ^ 2)
    (hcs : C ^ 2 ≤ N * S) :
    N - 4 * alpha ^ 2 * S ≤ 0 := by
  have h := resonance_cauchy_forces_scaled_shear hN hres hcs
  linarith

theorem exact_resonance_allows_zero_scaled_gap :
    let alpha : ℝ := 1
    let N : ℝ := 4
    let S : ℝ := 1
    let C : ℝ := 2
    0 < N ∧
      (2 * alpha * C) ^ 2 = N ^ 2 ∧
      C ^ 2 ≤ N * S ∧
      N - 4 * alpha ^ 2 * S = 0 := by
  norm_num

theorem exact_resonance_allows_strict_negative_scaled_gap :
    let alpha : ℝ := 1
    let N : ℝ := 4
    let S : ℝ := 2
    let C : ℝ := 2
    0 < N ∧
      (2 * alpha * C) ^ 2 = N ^ 2 ∧
      C ^ 2 ≤ N * S ∧
      N - 4 * alpha ^ 2 * S < 0 := by
  norm_num

theorem resonance_cauchy_does_not_force_positive_scaled_gap :
    ¬ (∀ alpha N S C : ℝ,
        0 < N →
        (2 * alpha * C) ^ 2 = N ^ 2 →
        C ^ 2 ≤ N * S →
        0 < N - 4 * alpha ^ 2 * S) := by
  intro h
  have hbad := h (1 : ℝ) 4 2 2 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad

#print axioms resonance_cauchy_forces_scaled_shear
#print axioms scaled_resonance_gap_nonpositive
#print axioms exact_resonance_allows_zero_scaled_gap
#print axioms exact_resonance_allows_strict_negative_scaled_gap
#print axioms resonance_cauchy_does_not_force_positive_scaled_gap

end NSPVWeightedResonanceSignFirewall
