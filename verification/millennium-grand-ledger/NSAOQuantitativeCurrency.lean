import Mathlib

/-!
# Conditional AO retuning and normalized intermittent scaling

This file isolates two exact finite cores from the current Navier--Stokes
Albritton--Ożański (AO) route.

* The four sign assumptions extracted from the Batchelor double-critical
  formulas imply a strictly negative Jacobian.  Cramer's rule and Banach's
  fixed-point theorem then give explicit algebraic/nonlinear retuning
  certificates.
* A conditional normalized scaling ledger uses a small energy-decay tax.  Its
  finite nominal partial sums are uniformly bounded while viscosity and axial
  modulation have two and three powers of slack relative to nominal growth.

Nothing here asserts persistence of the Euler eigenmode under windowing, an
exact Navier--Stokes relay, infinite iteration, or blow-up.
-/

namespace NSAOQuantitativeCurrency

noncomputable section

open scoped BigOperators

/-! ## Batchelor transversality and retuning -/

/-- The sign pattern in the AO Batchelor formulas forces the full two-variable
Jacobian `-2 * beta * F1_r - F1_beta * g'` to be strictly negative. -/
theorem batchelor_jacobian_sign_implication
    {beta F1r F1beta gprime : ℝ}
    (hbeta : 0 < beta)
    (hF1r : 0 < F1r)
    (hF1beta : F1beta < 0)
    (hgprime : gprime < 0) :
    -2 * beta * F1r - F1beta * gprime < 0 := by
  have hfirst : 0 < 2 * beta * F1r := by positivity
  have hsecond : 0 < F1beta * gprime :=
    mul_pos_of_neg_of_neg hF1beta hgprime
  linarith

/-- Exact Cramer retuning for two affine critical-point residuals. -/
theorem cramer_retuning
    {a b c d u v : ℝ}
    (hdet : a * d - b * c ≠ 0) :
    let x := (b * v - d * u) / (a * d - b * c)
    let y := (c * u - a * v) / (a * d - b * c)
    a * x + b * y + u = 0 ∧ c * x + d * y + v = 0 := by
  dsimp
  have hunit :
      (a * d - b * c) * (a * d - b * c)⁻¹ = (1 : ℝ) :=
    mul_inv_cancel₀ hdet
  constructor
  · simp only [div_eq_mul_inv]
    calc
      a * ((b * v - d * u) * (a * d - b * c)⁻¹) +
          b * ((c * u - a * v) * (a * d - b * c)⁻¹) + u =
          (a * (b * v - d * u) + b * (c * u - a * v)) *
            (a * d - b * c)⁻¹ + u := by ring
      _ = -u * (a * d - b * c) * (a * d - b * c)⁻¹ + u := by
        rw [show
          a * (b * v - d * u) + b * (c * u - a * v) =
            -u * (a * d - b * c) by ring]
      _ =
          -u * ((a * d - b * c) * (a * d - b * c)⁻¹) + u := by ring
      _ = 0 := by rw [hunit]; ring
  · simp only [div_eq_mul_inv]
    calc
      c * ((b * v - d * u) * (a * d - b * c)⁻¹) +
          d * ((c * u - a * v) * (a * d - b * c)⁻¹) + v =
          (c * (b * v - d * u) + d * (c * u - a * v)) *
            (a * d - b * c)⁻¹ + v := by ring
      _ = -v * (a * d - b * c) * (a * d - b * c)⁻¹ + v := by
        rw [show
          c * (b * v - d * u) + d * (c * u - a * v) =
            -v * (a * d - b * c) by ring]
      _ =
          -v * ((a * d - b * c) * (a * d - b * c)⁻¹) + v := by ring
      _ = 0 := by rw [hunit]; ring

/-- A strict reference margin survives an additive perturbation bounded by half
the recorded reference value. -/
theorem open_margin_survives
    {reference margin error : ℝ}
    (href : 2 * margin ≤ reference)
    (herror : |error| ≤ margin) :
    margin ≤ reference + error := by
  have hlower : -|error| ≤ error := neg_abs_le error
  linarith

/-- Pointwise algebra behind the standard axisymmetric window corrector.  If
the radial flux derivative is `-chiPrime * r * W` and the axial derivative is
`chiPrime * W`, the cylindrical divergence cancels away from the axis.  A PDE
construction must still prove these derivative identities and regularity at
`r = 0`; neither is hidden in this scalar lemma. -/
theorem axisymmetric_window_divergence_cancels
    {r W chiPrime radialFluxDerivative axialDerivative : ℝ}
    (hr : r ≠ 0)
    (hradial : radialFluxDerivative = -chiPrime * r * W)
    (haxial : axialDerivative = chiPrime * W) :
    radialFluxDerivative / r + axialDerivative = 0 := by
  rw [hradial, haxial]
  field_simp [hr] <;> ring

/-- If a radial corrector has a nonzero limiting flux coefficient `flux`, its
cylindrical energy density has the exact `flux^2 / r` tail.  The analytic fact
that the integral of `1/r` diverges is deliberately not smuggled into this
algebraic statement. -/
def asymptoticRadialCorrector (flux r : ℝ) : ℝ := flux / r

theorem flux_corrector_density
    {flux r : ℝ} (hr : r ≠ 0) :
    r * asymptoticRadialCorrector flux r ^ 2 = flux ^ 2 / r := by
  unfold asymptoticRadialCorrector
  field_simp [hr]
  ring

/-- The preconditioned fixed-point map used for nonlinear retuning. -/
def preconditionedMap
    {X : Type*} [Sub X] (L F : X → X) (x : X) : X :=
  x - L (F x)

/-- If the preconditioner is injective and preserves zero, fixed points of the
preconditioned map are exactly zeros of the residual. -/
theorem fixed_point_preconditioned_iff_root
    {X : Type*} [AddCommGroup X]
    {L F : X → X} (hL0 : L 0 = 0) (hLinj : Function.Injective L) (x : X) :
    Function.IsFixedPt (preconditionedMap L F) x ↔ F x = 0 := by
  constructor
  · intro hfixed
    have hzero : L (F x) = 0 := by
      exact sub_eq_self.mp hfixed
    apply hLinj
    rw [hL0]
    exact hzero
  · intro hroot
    simp [Function.IsFixedPt, preconditionedMap, hroot, hL0]

/-- A global contraction certificate for a preconditioned residual produces an
exact nonlinear root and an explicit a-posteriori displacement bound.  The AO
PDE gate is to prove this contraction on the relevant complete profile ball. -/
theorem contraction_retunes_exactly
    {X : Type*} [NormedAddCommGroup X] [CompleteSpace X] [Nonempty X]
    {K : NNReal} {L F : X → X}
    (hL0 : L 0 = 0)
    (hLinj : Function.Injective L)
    (hcontract : ContractingWith K (preconditionedMap L F))
    (x0 : X) :
    ∃ x : X,
      F x = 0 ∧
      dist x0 x ≤
        dist x0 (preconditionedMap L F x0) / (1 - (K : ℝ)) := by
  let x := ContractingWith.fixedPoint (preconditionedMap L F) hcontract
  have hfixed : Function.IsFixedPt (preconditionedMap L F) x :=
    ContractingWith.fixedPoint_isFixedPt hcontract
  have hroot : F x = 0 :=
    (fixed_point_preconditioned_iff_root hL0 hLinj x).mp hfixed
  have hbound :
      dist x0 x ≤
        dist x0 (preconditionedMap L F x0) / (1 - (K : ℝ)) := by
    exact ContractingWith.dist_fixedPoint_le hcontract x0
  exact ⟨x, hroot, hbound⟩

/-! ## A bounded conditional dyadic scaling ledger -/

/-- The shell index starts at physical shell `2`, avoiding the degenerate
`R = 1` scale where asymptotic margin ratios equal one. -/
def shell (j : ℕ) : ℝ := (2 : ℝ) ^ (j + 1)

/-- These are normalized scaling currencies, not norms of a constructed
velocity field.  The PDE bridge must realize them with two-sided norm bounds. -/
def carrier (j : ℕ) : ℝ := shell j ^ 8
def amplitude (j : ℕ) : ℝ := shell j ^ 10
def axialLength (j : ℕ) : ℝ := 1 / shell j ^ 5
def nominalActiveVolume (j : ℕ) : ℝ := 1 / shell j ^ 21
def nominalPumpEnergy (j : ℕ) : ℝ := amplitude j ^ 2 * nominalActiveVolume j
def nominalLocalGrowth (j : ℕ) : ℝ := amplitude j * carrier j
def nominalViscosityScale (j : ℕ) : ℝ := carrier j ^ 2
def envelopeBandwidth (j : ℕ) : ℝ := shell j ^ 5

/-- For general shell exponents, these are respectively the decay exponent of
the pump energy, the growth-over-viscosity gap, and the carrier-over-modulation
gap.  Positive values are the three strict currencies required by this route. -/
def energyDecayExponent (p q s : ℝ) : ℝ := 2 * p + q - 2 * s
def viscosityGapExponent (p s : ℝ) : ℝ := s - p
def modulationGapExponent (p q : ℝ) : ℝ := p - q

/-- Equalizing the three dyadic margins forces the unique balanced ray
`(p,q,s) = (4m,3m,5m)`.  This does not say that equal margins are optimal; the
chosen scaling below deliberately buys unequal extra PDE slack. -/
theorem balanced_margin_ray
    {p q s m : ℝ}
    (henergy : energyDecayExponent p q s = m)
    (hviscous : viscosityGapExponent p s = m)
    (hmodulation : modulationGapExponent p q = m) :
    p = 4 * m ∧ q = 3 * m ∧ s = 5 * m := by
  unfold energyDecayExponent viscosityGapExponent modulationGapExponent at *
  constructor
  · linarith
  constructor <;> linarith

/-- Conversely every point on the balanced ray has all three margins exactly
`m`. -/
theorem balanced_margin_ray_converse (m : ℝ) :
    energyDecayExponent (4 * m) (3 * m) (5 * m) = m ∧
      viscosityGapExponent (4 * m) (5 * m) = m ∧
      modulationGapExponent (4 * m) (3 * m) = m := by
  unfold energyDecayExponent viscosityGapExponent modulationGapExponent
  constructor
  · ring
  constructor <;> ring

/-- The chosen exponents retain energy decay one but buy two powers of viscous
slack and three powers of modulation slack. -/
theorem slack_margin_choice :
    energyDecayExponent 8 5 10 = 1 ∧
      viscosityGapExponent 8 10 = 2 ∧
      modulationGapExponent 8 5 = 3 := by
  norm_num [energyDecayExponent, viscosityGapExponent, modulationGapExponent]

theorem shell_ne_zero (j : ℕ) : shell j ≠ 0 := by
  unfold shell
  exact pow_ne_zero (j + 1) (by norm_num)

/-- The nominal energy tax is exactly one inverse shell: `2^{-(j+1)}`. -/
theorem nominal_pump_energy_identity (j : ℕ) :
    nominalPumpEnergy j = 1 / shell j := by
  unfold nominalPumpEnergy amplitude nominalActiveVolume
  field_simp [shell_ne_zero j]

/-- The nominal local instability clock has exponent `18/8 = 9/4` in the
physical carrier. -/
theorem nominal_local_growth_identity (j : ℕ) :
    nominalLocalGrowth j = shell j ^ 18 := by
  unfold nominalLocalGrowth amplitude carrier
  ring

/-- Carrier-scale viscosity is two inverse shells below nominal local growth. -/
theorem viscosity_to_growth_identity (j : ℕ) :
    nominalViscosityScale j / nominalLocalGrowth j = 1 / shell j ^ 2 := by
  rw [nominal_local_growth_identity]
  unfold nominalViscosityScale carrier
  field_simp [shell_ne_zero j]

/-- Slow axial modulation is three inverse shells below the carrier. -/
theorem modulation_to_carrier_identity (j : ℕ) :
    envelopeBandwidth j / carrier j = 1 / shell j ^ 3 := by
  unfold envelopeBandwidth carrier
  field_simp [shell_ne_zero j]

theorem inverse_shell_eq_half_pow_succ (j : ℕ) :
    1 / shell j = (1 / 2 : ℝ) ^ (j + 1) := by
  simp [shell]

/-- Exact finite geometric-energy ledger. -/
theorem dyadic_energy_partial_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 1))
      = 1 - (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

/-- All finite collections have total normalized nominal pump currency at most
`1`.  This is not an `L^2` theorem for a constructed velocity field. -/
theorem dyadic_nominal_pump_energy_uniformly_bounded (n : ℕ) :
    (∑ j ∈ Finset.range n, nominalPumpEnergy j) ≤ 1 := by
  simp_rw [nominal_pump_energy_identity, inverse_shell_eq_half_pow_succ]
  rw [dyadic_energy_partial_sum]
  have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  linarith

structure DyadicAOScalingLedger : Prop where
  nominalEnergy : ∀ j, nominalPumpEnergy j = (1 / 2 : ℝ) ^ (j + 1)
  boundedNominalEnergy : ∀ n,
    (∑ j ∈ Finset.range n, nominalPumpEnergy j) ≤ 1
  nominalGrowth : ∀ j, nominalLocalGrowth j = shell j ^ 18
  viscousMargin : ∀ j,
    nominalViscosityScale j / nominalLocalGrowth j = 1 / shell j ^ 2
  modulationMargin : ∀ j,
    envelopeBandwidth j / carrier j = 1 / shell j ^ 3

/-- One kernel object packages the corrected conditional scaling arithmetic. -/
theorem dyadic_ao_scaling_ledger : DyadicAOScalingLedger where
  nominalEnergy := fun j =>
    (nominal_pump_energy_identity j).trans (inverse_shell_eq_half_pow_succ j)
  boundedNominalEnergy := dyadic_nominal_pump_energy_uniformly_bounded
  nominalGrowth := nominal_local_growth_identity
  viscousMargin := viscosity_to_growth_identity
  modulationMargin := modulation_to_carrier_identity

/-- The finite, theorem-bearing portion of the current AO gate.  The nonlinear
contraction theorem above is kept separately because its profile space is
polymorphic; the PDE work is precisely to instantiate it. -/
structure AOConditionalScalingCore : Prop where
  transversality : ∀ {beta F1r F1beta gprime : ℝ},
    0 < beta → 0 < F1r → F1beta < 0 → gprime < 0 →
      -2 * beta * F1r - F1beta * gprime < 0
  linearRetuning : ∀ {a b c d u v : ℝ}, a * d - b * c ≠ 0 →
    let x := (b * v - d * u) / (a * d - b * c)
    let y := (c * u - a * v) / (a * d - b * c)
    a * x + b * y + u = 0 ∧ c * x + d * y + v = 0
  marginStability : ∀ {reference margin error : ℝ},
    2 * margin ≤ reference → |error| ≤ margin →
      margin ≤ reference + error
  divergenceCancellation : ∀ {r W chiPrime radialFluxDerivative axialDerivative : ℝ},
    r ≠ 0 →
    radialFluxDerivative = -chiPrime * r * W →
    axialDerivative = chiPrime * W →
    radialFluxDerivative / r + axialDerivative = 0
  balancedMargins : ∀ {p q s m : ℝ},
    energyDecayExponent p q s = m →
    viscosityGapExponent p s = m →
    modulationGapExponent p q = m →
    p = 4 * m ∧ q = 3 * m ∧ s = 5 * m
  slackMargins :
    energyDecayExponent 8 5 10 = 1 ∧
      viscosityGapExponent 8 10 = 2 ∧
      modulationGapExponent 8 5 = 3
  fluxTailDensity : ∀ {flux r : ℝ}, r ≠ 0 →
    r * asymptoticRadialCorrector flux r ^ 2 = flux ^ 2 / r
  scalingLedger : DyadicAOScalingLedger

theorem ao_conditional_scaling_core : AOConditionalScalingCore where
  transversality := fun hbeta hF1r hF1beta hgprime =>
    batchelor_jacobian_sign_implication hbeta hF1r hF1beta hgprime
  linearRetuning := fun hdet => cramer_retuning hdet
  marginStability := fun href herror => open_margin_survives href herror
  divergenceCancellation := fun hr hradial haxial =>
    axisymmetric_window_divergence_cancels hr hradial haxial
  balancedMargins := fun henergy hviscous hmodulation =>
    balanced_margin_ray henergy hviscous hmodulation
  slackMargins := slack_margin_choice
  fluxTailDensity := flux_corrector_density
  scalingLedger := dyadic_ao_scaling_ledger

#print axioms batchelor_jacobian_sign_implication
#print axioms cramer_retuning
#print axioms open_margin_survives
#print axioms axisymmetric_window_divergence_cancels
#print axioms flux_corrector_density
#print axioms fixed_point_preconditioned_iff_root
#print axioms contraction_retunes_exactly
#print axioms balanced_margin_ray
#print axioms balanced_margin_ray_converse
#print axioms slack_margin_choice
#print axioms nominal_pump_energy_identity
#print axioms viscosity_to_growth_identity
#print axioms dyadic_nominal_pump_energy_uniformly_bounded
#print axioms dyadic_ao_scaling_ledger
#print axioms ao_conditional_scaling_core

end

end NSAOQuantitativeCurrency
