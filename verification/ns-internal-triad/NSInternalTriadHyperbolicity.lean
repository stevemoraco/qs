import Mathlib

/-!
# Internal energy-paired triad hyperbolicity

This file formalizes only the finite algebra of one low mode coupled to two
high modes with equal viscosity. It does not formalize Fourier/helical modes,
Leray projection, Navier–Stokes solutions, invariant manifolds, or blow-up.
-/

namespace NSInternalTriadHyperbolicity

/-- Symmetric high-mode amplitude. -/
noncomputable def pairMean (y z : ℝ) : ℝ := (y + z) / 2

/-- Antisymmetric high-mode defect. -/
noncomputable def pairDefect (y z : ℝ) : ℝ := (y - z) / 2

/-- Reconstruction of a high-mode pair from mean and defect. -/
def fromMeanDefect (s d : ℝ) : ℝ × ℝ := (s + d, s - d)

/-- Energy-paired low-mode feedback. -/
def lowRate (a y z : ℝ) : ℝ := -2 * a * y * z

/-- First high-mode rate with common viscosity. -/
def highRate₁ (a μ x y z : ℝ) : ℝ := a * x * z - μ * y

/-- Second high-mode rate with common viscosity. -/
def highRate₂ (a μ x y z : ℝ) : ℝ := a * x * y - μ * z

/-- BANKER: mean/defect reconstruction is exact. -/
theorem reconstruction_exact (s d : ℝ) :
    pairMean (fromMeanDefect s d).1 (fromMeanDefect s d).2 = s ∧
      pairDefect (fromMeanDefect s d).1 (fromMeanDefect s d).2 = d := by
  constructor <;> unfold pairMean pairDefect fromMeanDefect <;> ring

/-- BANKER: the symmetric high-mode receives the catalytic growth rate. -/
theorem symmetric_rate_identity (a μ x y z : ℝ) :
    pairMean (highRate₁ a μ x y z) (highRate₂ a μ x y z) =
      (a * x - μ) * pairMean y z := by
  unfold pairMean highRate₁ highRate₂
  ring

/-- BANKER: the antisymmetric defect receives the opposite catalytic sign. -/
theorem antisymmetric_rate_identity (a μ x y z : ℝ) :
    pairDefect (highRate₁ a μ x y z) (highRate₂ a μ x y z) =
      -(a * x + μ) * pairDefect y z := by
  unfold pairDefect highRate₁ highRate₂
  ring

/-- Product of the high amplitudes is mean-square minus defect-square. -/
theorem pair_product_decomposition (y z : ℝ) :
    y * z = pairMean y z ^ 2 - pairDefect y z ^ 2 := by
  unfold pairMean pairDefect
  ring

/-- The low feedback expressed in tangent/normal coordinates. -/
theorem low_rate_mean_defect (a y z : ℝ) :
    lowRate a y z =
      -2 * a * (pairMean y z ^ 2 - pairDefect y z ^ 2) := by
  rw [← pair_product_decomposition]
  rfl

/-- The diagonal high-mode manifold is invariant at the finite rate level. -/
theorem diagonal_is_invariant (a μ x y : ℝ) :
    highRate₁ a μ x y y = highRate₂ a μ x y y := by
  unfold highRate₁ highRate₂
  ring

/-- Exact viscous energy balance: the quadratic triad coupling is energy-skew. -/
theorem viscous_energy_identity (a μ x y z : ℝ) :
    x * lowRate a y z +
        y * highRate₁ a μ x y z +
        z * highRate₂ a μ x y z =
      -μ * (y ^ 2 + z ^ 2) := by
  unfold lowRate highRate₁ highRate₂
  ring

/-- Inviscid specialization of the exact energy law. -/
theorem inviscid_energy_conservation (a x y z : ℝ) :
    x * lowRate a y z +
        y * highRate₁ a 0 x y z +
        z * highRate₂ a 0 x y z = 0 := by
  simpa using viscous_energy_identity a 0 x y z

/-- CRITIC/CLEANER: supercritical tangent activation with nonnegative viscosity
forces strict decay of the internal antisymmetric normal mode. -/
theorem activation_implies_normal_decay
    {a μ x : ℝ}
    (hμ : 0 ≤ μ)
    (hact : μ < a * x) :
    0 < a * x - μ ∧ -(a * x + μ) < 0 := by
  constructor
  · linarith
  · linarith

/-- Exact tangent-normal rate separation. -/
theorem tangent_normal_gap_identity (a μ x : ℝ) :
    (a * x - μ) - (-(a * x + μ)) = 2 * a * x := by
  ring

/-- Two intended high pairs close through the sum of tangent squares minus
normal-defect squares. -/
theorem two_pair_output_decomposition
    (y₁ z₁ y₂ z₂ : ℝ) :
    y₁ * z₁ + y₂ * z₂ =
      (pairMean y₁ z₁ ^ 2 + pairMean y₂ z₂ ^ 2) -
        (pairDefect y₁ z₁ ^ 2 + pairDefect y₂ z₂ ^ 2) := by
  rw [pair_product_decomposition, pair_product_decomposition]
  ring

/-- On the product diagonal, unequal tangent amplitudes still contribute
coherently through their aggregate square. -/
theorem two_pair_diagonal_output (s₁ s₂ : ℝ) :
    (fromMeanDefect s₁ 0).1 * (fromMeanDefect s₁ 0).2 +
        (fromMeanDefect s₂ 0).1 * (fromMeanDefect s₂ 0).2 =
      s₁ ^ 2 + s₂ ^ 2 := by
  unfold fromMeanDefect
  ring

/-- A common tangent multiplier closes exactly on the aggregate square. -/
theorem two_pair_aggregate_square_rate (r s₁ s₂ : ℝ) :
    2 * s₁ * (r * s₁) + 2 * s₂ * (r * s₂) =
      2 * r * (s₁ ^ 2 + s₂ ^ 2) := by
  ring

/-- Normal aggregate squares have the exact opposite-sign rate. -/
theorem two_pair_defect_square_rate (q d₁ d₂ : ℝ) :
    2 * d₁ * (-q * d₁) + 2 * d₂ * (-q * d₂) =
      -2 * q * (d₁ ^ 2 + d₂ ^ 2) := by
  ring

/-- The aggregate shell closure does not require equality of the individual
symmetric molecule amplitudes. -/
theorem unequal_tangent_amplitudes_still_close
    (a x μ s₁ s₂ : ℝ) :
    2 * s₁ * ((a * x - μ) * s₁) +
        2 * s₂ * ((a * x - μ) * s₂) =
      2 * (a * x - μ) * (s₁ ^ 2 + s₂ ^ 2) := by
  ring

#print axioms reconstruction_exact
#print axioms symmetric_rate_identity
#print axioms antisymmetric_rate_identity
#print axioms pair_product_decomposition
#print axioms low_rate_mean_defect
#print axioms diagonal_is_invariant
#print axioms viscous_energy_identity
#print axioms inviscid_energy_conservation
#print axioms activation_implies_normal_decay
#print axioms tangent_normal_gap_identity
#print axioms two_pair_output_decomposition
#print axioms two_pair_diagonal_output
#print axioms two_pair_aggregate_square_rate
#print axioms two_pair_defect_square_rate
#print axioms unequal_tangent_amplitudes_still_close

end NSInternalTriadHyperbolicity
