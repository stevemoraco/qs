import Mathlib

/-!
# Quantitative AO retuning and summable intermittent currency

This file isolates two exact finite cores from the current Navier--Stokes
Albritton--Ożański (AO) route.

* The Batchelor double-critical equations have a strictly negative Jacobian
  under the four source sign conditions.  Cramer's rule and Banach's fixed-point
  theorem then give explicit algebraic/nonlinear retuning certificates.
* A corrected dyadic window uses a small energy-decay tax.  Its pump energies
  are summable while both viscosity and axial modulation remain one strict
  dyadic power below the local AO growth scale.

Nothing here asserts persistence of the Euler eigenmode under windowing, an
exact Navier--Stokes relay, infinite iteration, or blow-up.
-/

namespace NSAOQuantitativeCurrency

noncomputable section

open scoped BigOperators

/-! ## Batchelor transversality and retuning -/

/-- The sign pattern in the AO Batchelor formulas forces the full two-variable
Jacobian `-2 * beta * F1_r - F1_beta * g'` to be strictly negative. -/
theorem batchelor_jacobian_negative
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

/-! ## A summable dyadic finite-energy/supercritical currency -/

/-- The shell variable is `2^j`.  The physical carrier is its fourth power,
so every fractional scaling exponent below becomes an integer power. -/
def shell (j : ℕ) : ℝ := (2 : ℝ) ^ j

def carrier (j : ℕ) : ℝ := shell j ^ 4
def amplitude (j : ℕ) : ℝ := shell j ^ 5
def axialLength (j : ℕ) : ℝ := 1 / shell j ^ 3
def activeVolume (j : ℕ) : ℝ := 1 / shell j ^ 11
def pumpEnergy (j : ℕ) : ℝ := amplitude j ^ 2 * activeVolume j
def localGrowth (j : ℕ) : ℝ := amplitude j * carrier j
def viscosityScale (j : ℕ) : ℝ := carrier j ^ 2
def envelopeBandwidth (j : ℕ) : ℝ := shell j ^ 3

/-- For general shell exponents, these are respectively the decay exponent of
the pump energy, the growth-over-viscosity gap, and the carrier-over-modulation
gap.  Positive values are the three strict currencies required by this route. -/
def energyDecayExponent (p q s : ℝ) : ℝ := 2 * p + q - 2 * s
def viscosityGapExponent (p s : ℝ) : ℝ := s - p
def modulationGapExponent (p q : ℝ) : ℝ := p - q

/-- Equalizing the three dyadic margins forces the unique balanced ray
`(p,q,s) = (4m,3m,5m)`.  In particular `m=1` explains the integer exponents
used below; they are not an arbitrary numerical guess. -/
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

theorem shell_ne_zero (j : ℕ) : shell j ≠ 0 := by
  unfold shell
  exact pow_ne_zero j (by norm_num)

/-- The energy tax is exactly one inverse shell: `2^{-j}`. -/
theorem pump_energy_identity (j : ℕ) :
    pumpEnergy j = 1 / shell j := by
  unfold pumpEnergy amplitude activeVolume
  field_simp [shell_ne_zero j]

/-- The local instability clock has exponent `9/4` in the physical carrier. -/
theorem local_growth_identity (j : ℕ) :
    localGrowth j = shell j ^ 9 := by
  unfold localGrowth amplitude carrier
  ring

/-- Carrier-scale viscosity is one inverse shell below local growth. -/
theorem viscosity_to_growth_identity (j : ℕ) :
    viscosityScale j / localGrowth j = 1 / shell j := by
  rw [local_growth_identity]
  unfold viscosityScale carrier
  field_simp [shell_ne_zero j]

/-- Slow axial modulation has the same one-inverse-shell relative margin. -/
theorem modulation_to_carrier_identity (j : ℕ) :
    envelopeBandwidth j / carrier j = 1 / shell j := by
  unfold envelopeBandwidth carrier
  field_simp [shell_ne_zero j]

theorem inverse_shell_eq_half_pow (j : ℕ) :
    1 / shell j = (1 / 2 : ℝ) ^ j := by
  simp [shell]

/-- Exact finite geometric-energy ledger. -/
theorem dyadic_energy_partial_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j)
      = 2 - 2 * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

/-- All finite collections of preloaded dyadic pumps have total kinetic-energy
currency at most `2`; hence the corrected scaling removes the earlier
shellwise-`O(1)` non-summability defect. -/
theorem dyadic_pump_energy_uniformly_bounded (n : ℕ) :
    (∑ j ∈ Finset.range n, pumpEnergy j) ≤ 2 := by
  simp_rw [pump_energy_identity, inverse_shell_eq_half_pow]
  rw [dyadic_energy_partial_sum]
  have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  linarith

structure DyadicAOCurrency : Prop where
  energy : ∀ j, pumpEnergy j = (1 / 2 : ℝ) ^ j
  finiteEnergy : ∀ n, (∑ j ∈ Finset.range n, pumpEnergy j) ≤ 2
  growth : ∀ j, localGrowth j = shell j ^ 9
  viscousMargin : ∀ j, viscosityScale j / localGrowth j = (1 / 2 : ℝ) ^ j
  modulationMargin : ∀ j, envelopeBandwidth j / carrier j = (1 / 2 : ℝ) ^ j

/-- One kernel object packages the corrected finite-energy, growth, viscosity,
and modulation arithmetic. -/
theorem dyadic_ao_currency : DyadicAOCurrency where
  energy := fun j => (pump_energy_identity j).trans (inverse_shell_eq_half_pow j)
  finiteEnergy := dyadic_pump_energy_uniformly_bounded
  growth := local_growth_identity
  viscousMargin := fun j =>
    (viscosity_to_growth_identity j).trans (inverse_shell_eq_half_pow j)
  modulationMargin := fun j =>
    (modulation_to_carrier_identity j).trans (inverse_shell_eq_half_pow j)

/-- The finite, theorem-bearing portion of the current AO gate.  The nonlinear
contraction theorem above is kept separately because its profile space is
polymorphic; the PDE work is precisely to instantiate it. -/
structure AOQuantitativeCore : Prop where
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
  currency : DyadicAOCurrency

theorem ao_quantitative_core : AOQuantitativeCore where
  transversality := fun hbeta hF1r hF1beta hgprime =>
    batchelor_jacobian_negative hbeta hF1r hF1beta hgprime
  linearRetuning := fun hdet => cramer_retuning hdet
  marginStability := fun href herror => open_margin_survives href herror
  divergenceCancellation := fun hr hradial haxial =>
    axisymmetric_window_divergence_cancels hr hradial haxial
  balancedMargins := fun henergy hviscous hmodulation =>
    balanced_margin_ray henergy hviscous hmodulation
  currency := dyadic_ao_currency

#print axioms batchelor_jacobian_negative
#print axioms cramer_retuning
#print axioms open_margin_survives
#print axioms axisymmetric_window_divergence_cancels
#print axioms fixed_point_preconditioned_iff_root
#print axioms contraction_retunes_exactly
#print axioms balanced_margin_ray
#print axioms balanced_margin_ray_converse
#print axioms pump_energy_identity
#print axioms viscosity_to_growth_identity
#print axioms dyadic_pump_energy_uniformly_bounded
#print axioms dyadic_ao_currency
#print axioms ao_quantitative_core

end

end NSAOQuantitativeCurrency
