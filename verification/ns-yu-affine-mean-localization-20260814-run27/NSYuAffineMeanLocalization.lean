import Mathlib

/-!
# Navier--Stokes / Yu affine mean-localization finite core

Finite real algebra only.  This file does **not** formalize the Navier--Stokes
PDE, Yu's filtered-vorticity estimates, Poincare's inequality, Stokes/coarea,
harmonic interior estimates, Type-I compactness, or any Clay conclusion.

It formalizes the reusable scalar endgame behind the following human theorem
interface.  For a spatially constant exterior strain, split filtered vorticity
into its spatial mean plus a zero-mean fluctuation.  Poincare sends the
fluctuation work to diffusion; Stokes/coarea sends the mean mode to a cutoff
shell/localization budget.  A separated harmonic source gives an additional
core/source scale margin.
-/

noncomputable section

namespace NSYuAffineMeanLocalization

/-- If an affine-work fluctuation is bounded by `K * variance`, and the variance
has a Poincare-type bound, then the fluctuation work is destination-visible to
diffusion. -/
theorem fluctuation_work_absorbed
    (work K variance Cp scale D : ℝ)
    (hK : 0 ≤ K)
    (hwork : work ≤ K * variance)
    (hvar : variance ≤ Cp * scale ^ 2 * D) :
    work ≤ K * Cp * scale ^ 2 * D := by
  calc
    work ≤ K * variance := hwork
    _ ≤ K * (Cp * scale ^ 2 * D) :=
      mul_le_mul_of_nonneg_left hvar hK
    _ = K * Cp * scale ^ 2 * D := by ring

/-- Abstract mean/fluctuation package: once the mean mode is charged to a
localization budget and the fluctuation is charged to diffusion, their sum has
no third destination. -/
theorem mean_and_fluctuation_close_affine_work
    (work meanWork fluctWork localization eta D : ℝ)
    (hwork : work ≤ meanWork + fluctWork)
    (hmean : meanWork ≤ localization)
    (hfluct : fluctWork ≤ eta * D) :
    work ≤ localization + eta * D := by
  calc
    work ≤ meanWork + fluctWork := hwork
    _ ≤ localization + eta * D := add_le_add hmean hfluct

/-- A source-facing version.  `meanEnergy <= shellCharge` is the scalar shadow
of the Stokes/coarea boundary charge, while `variance <= Cp * scale^2 * D` is
the scalar shadow of Poincare. -/
theorem affine_work_to_shell_and_diffusion
    (work K meanEnergy variance shellCharge Cp scale D : ℝ)
    (hK : 0 ≤ K)
    (hwork : work ≤ K * (meanEnergy + variance))
    (hmean : meanEnergy ≤ shellCharge)
    (hvar : variance ≤ Cp * scale ^ 2 * D) :
    work ≤ K * shellCharge + K * Cp * scale ^ 2 * D := by
  have hsum :
      meanEnergy + variance ≤ shellCharge + Cp * scale ^ 2 * D :=
    add_le_add hmean hvar
  calc
    work ≤ K * (meanEnergy + variance) := hwork
    _ ≤ K * (shellCharge + Cp * scale ^ 2 * D) :=
      mul_le_mul_of_nonneg_left hsum hK
    _ = K * shellCharge + K * Cp * scale ^ 2 * D := by ring

/-- If the Poincare coefficient is below the available diffusion margin and the
mean mode is already paid by localization, the entire affine work closes. -/
theorem affine_work_strict_budget
    (work K meanEnergy variance shellCharge Cp scale D eta localization : ℝ)
    (hK : 0 ≤ K)
    (hD : 0 ≤ D)
    (hwork : work ≤ K * (meanEnergy + variance))
    (hmean : meanEnergy ≤ shellCharge)
    (hvar : variance ≤ Cp * scale ^ 2 * D)
    (hsmall : K * Cp * scale ^ 2 ≤ eta)
    (hshell : K * shellCharge ≤ localization) :
    work ≤ localization + eta * D := by
  have hbase :=
    affine_work_to_shell_and_diffusion
      work K meanEnergy variance shellCharge Cp scale D hK hwork hmean hvar
  have hdiff : K * Cp * scale ^ 2 * D ≤ eta * D := by
    exact mul_le_mul_of_nonneg_right hsmall hD
  exact le_trans hbase (add_le_add hshell hdiff)

/-- Core/source scale separation produces the expected quadratic margin.  This
is the scalar algebra behind `K ~ R^{-2}` and `scale <= theta * R`. -/
theorem separated_source_quadratic_margin
    (K C R scale theta : ℝ)
    (hK : 0 ≤ K)
    (hR : 0 ≤ R)
    (hscale : 0 ≤ scale)
    (htheta : 0 ≤ theta)
    (hsep : scale ≤ theta * R)
    (hsource : K * R ^ 2 ≤ C) :
    K * scale ^ 2 ≤ C * theta ^ 2 := by
  have hthetaR : 0 ≤ theta * R := mul_nonneg htheta hR
  have hsquare : scale ^ 2 ≤ (theta * R) ^ 2 := by
    nlinarith
  have hmul : K * scale ^ 2 ≤ K * (theta * R) ^ 2 :=
    mul_le_mul_of_nonneg_left hsquare hK
  have htheta2 : 0 ≤ theta ^ 2 := sq_nonneg theta
  calc
    K * scale ^ 2 ≤ K * (theta * R) ^ 2 := hmul
    _ = theta ^ 2 * (K * R ^ 2) := by ring
    _ ≤ theta ^ 2 * C := mul_le_mul_of_nonneg_left hsource htheta2
    _ = C * theta ^ 2 := by ring

/-- Diffusion alone cannot remove the spatial mean mode: a zero-variance,
zero-diffusion state may still carry strictly positive affine work. -/
theorem constant_mean_mode_blocks_diffusion_only
    (K : ℝ) (hK : 0 < K) :
    ∃ work meanEnergy variance D : ℝ,
      work = K * (meanEnergy + variance) ∧
      meanEnergy = 1 ∧
      variance = 0 ∧
      D = 0 ∧
      0 < work := by
  refine ⟨K, 1, 0, 0, ?_, rfl, rfl, rfl, hK⟩
  ring

#print axioms fluctuation_work_absorbed
#print axioms mean_and_fluctuation_close_affine_work
#print axioms affine_work_to_shell_and_diffusion
#print axioms affine_work_strict_budget
#print axioms separated_source_quadratic_margin
#print axioms constant_mean_mode_blocks_diffusion_only

end NSYuAffineMeanLocalization
