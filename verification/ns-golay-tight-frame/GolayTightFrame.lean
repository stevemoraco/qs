import Mathlib

/-!
# Golay translation-frame finite core

This file separates two exact finite ingredients for a proposed broad-packet
Navier--Stokes cascade embedding.

1. A matrix whose row Gram kernel is `C` times the identity has exact
   analysis--synthesis operator `C I`.
2. The length-four Golay pair

   `A = (1, 1, 1, -1)`, `B = (1, 1, -1, 1)`

   has complementary aperiodic autocorrelation, and its three-dimensional
   tensor family of eight species has summed correlation `512 δ₀`.

The bridge identifying translated lattice filters with the abstract matrix
rows is not formalized here.  Neither are helical polarizations, the Leray
projector, the Navier--Stokes bilinear symbol, leakage estimates, shell-model
shadowing, or finite-time breakdown.
-/

namespace Millennium.NavierStokes

section AbstractTightFrame

variable {ρ κ : Type*} [Fintype ρ] [Fintype κ]

/-- One analysis coefficient of a finite real filter matrix. -/
def analysisCoeff (K : ρ → κ → ℝ) (f : κ → ℝ) (r : ρ) : ℝ :=
  ∑ b, K r b * f b

/-- Entry of the row Gram kernel `KᵀK`. -/
def gramEntry (K : ρ → κ → ℝ) (a b : κ) : ℝ :=
  ∑ r, K r a * K r b

/-- Exact finite rearrangement of analysis followed by synthesis into the
Gram-kernel action. -/
theorem analysisSynthesis_eq_gramAction
    (K : ρ → κ → ℝ) (f : κ → ℝ) (a : κ) :
    (∑ r, K r a * analysisCoeff K f r)
      = ∑ b, gramEntry K a b * f b := by
  classical
  unfold analysisCoeff gramEntry
  calc
    (∑ r, K r a * (∑ b, K r b * f b))
        = ∑ r, ∑ b, K r a * (K r b * f b) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
    _ = ∑ b, ∑ r, K r a * (K r b * f b) := by
          rw [Finset.sum_comm]
    _ = ∑ b, (∑ r, K r a * K r b) * f b := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r hr
          ring

/-- A delta Gram kernel gives the exact tight-frame reconstruction operator
`C I`. -/
theorem tightFrame_reconstruction
    (K : ρ → κ → ℝ) (C : ℝ)
    (hGram : ∀ a b, gramEntry K a b = if a = b then C else 0)
    (f : κ → ℝ) (a : κ) :
    ∑ r, K r a * analysisCoeff K f r = C * f a := by
  classical
  calc
    (∑ r, K r a * analysisCoeff K f r)
        = ∑ b, gramEntry K a b * f b :=
          analysisSynthesis_eq_gramAction K f a
    _ = ∑ b, (if a = b then C else 0) * f b := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [hGram a b]
    _ = C * f a := by simp

/-- Specialization to the three-dimensional length-four Golay tensor
constant `8³ = 512`. -/
theorem golayConstant_tightFrame_reconstruction
    (K : ρ → κ → ℝ)
    (hGram : ∀ a b, gramEntry K a b = if a = b then 512 else 0)
    (f : κ → ℝ) (a : κ) :
    ∑ r, K r a * analysisCoeff K f r = 512 * f a := by
  exact tightFrame_reconstruction K 512 hGram f a

end AbstractTightFrame

section ExplicitGolayCertificate

/-- First length-four Golay word, extended by zero to all integer indices. -/
def golayA (n : ℤ) : ℤ :=
  if n = 0 then 1
  else if n = 1 then 1
  else if n = 2 then 1
  else if n = 3 then -1
  else 0

/-- Second length-four Golay word, extended by zero to all integer indices. -/
def golayB (n : ℤ) : ℤ :=
  if n = 0 then 1
  else if n = 1 then 1
  else if n = 2 then -1
  else if n = 3 then 1
  else 0

/-- Aperiodic correlation of a zero-extended length-four word. -/
def corr4 (u : ℤ → ℤ) (h : ℤ) : ℤ :=
  u 0 * u h
    + u 1 * u (1 + h)
    + u 2 * u (2 + h)
    + u 3 * u (3 + h)

/-- The exact seven-shift complementary autocorrelation table. -/
theorem golayPair_corr
    (h : ℤ) (hlo : (-3 : ℤ) ≤ h) (hhi : h ≤ 3) :
    corr4 golayA h + corr4 golayB h =
      if h = 0 then 8 else 0 := by
  interval_cases h <;> norm_num [corr4, golayA, golayB]

/-- Summed one-dimensional pair correlation. -/
def golayPairCorr (h : ℤ) : ℤ :=
  corr4 golayA h + corr4 golayB h

/-- Delta form of the one-dimensional certificate. -/
theorem golayPairCorr_delta
    (h : ℤ) (hlo : (-3 : ℤ) ≤ h) (hhi : h ≤ 3) :
    golayPairCorr h = if h = 0 then 8 else 0 := by
  simpa [golayPairCorr] using golayPair_corr h hlo hhi

/-- Sum of the eight tensor-species autocorrelations in three dimensions. -/
def golayEightSpeciesCorr (hx hy hz : ℤ) : ℤ :=
  let ax := corr4 golayA hx
  let bx := corr4 golayB hx
  let ay := corr4 golayA hy
  let by := corr4 golayB hy
  let az := corr4 golayA hz
  let bz := corr4 golayB hz
  ax * ay * az
    + ax * ay * bz
    + ax * by * az
    + ax * by * bz
    + bx * ay * az
    + bx * ay * bz
    + bx * by * az
    + bx * by * bz

/-- Tensoring three complementary pairs factors the eight-species sum into
three one-dimensional pair correlations. -/
theorem golayEightSpecies_factor (hx hy hz : ℤ) :
    golayEightSpeciesCorr hx hy hz =
      golayPairCorr hx * golayPairCorr hy * golayPairCorr hz := by
  simp only [golayEightSpeciesCorr, golayPairCorr]
  ring

/-- Exact three-dimensional tensor certificate: all nonzero translated
sidelobes vanish and the origin coefficient is `8³ = 512`. -/
theorem golayEightSpecies_delta
    (hx hy hz : ℤ)
    (hxl : (-3 : ℤ) ≤ hx) (hxu : hx ≤ 3)
    (hyl : (-3 : ℤ) ≤ hy) (hyu : hy ≤ 3)
    (hzl : (-3 : ℤ) ≤ hz) (hzu : hz ≤ 3) :
    golayEightSpeciesCorr hx hy hz =
      if hx = 0 ∧ hy = 0 ∧ hz = 0 then 512 else 0 := by
  rw [golayEightSpecies_factor]
  rw [golayPairCorr_delta hx hxl hxu]
  rw [golayPairCorr_delta hy hyl hyu]
  rw [golayPairCorr_delta hz hzl hzu]
  by_cases hx0 : hx = 0 <;>
    by_cases hy0 : hy = 0 <;>
      by_cases hz0 : hz = 0 <;>
        simp [hx0, hy0, hz0]

end ExplicitGolayCertificate

#print axioms analysisSynthesis_eq_gramAction
#print axioms tightFrame_reconstruction
#print axioms golayConstant_tightFrame_reconstruction
#print axioms golayPair_corr
#print axioms golayPairCorr_delta
#print axioms golayEightSpecies_factor
#print axioms golayEightSpecies_delta

end Millennium.NavierStokes
