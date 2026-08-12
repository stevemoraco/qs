import Mathlib

/-!
# Round 211 endpoint-stationarity finite countermodel

This file formalizes only polynomial equalities, homogeneity and a scalar
constraint countermodel. It does not formalize Navier--Stokes solutions,
axisymmetric variables, compactness, first-threshold packets, variational
calculus on function spaces, or the Clay problem.
-/

namespace Millennium
namespace Round211NavierStokes

/-- Quadratic scalar budget model. -/
def budget (x : ℚ) : ℚ := x ^ 2

/-- Cubic scalar transfer model. -/
def transfer (x : ℚ) : ℚ := x ^ 3

/-- Formal first-variation coefficient of `transfer - lambda * budget`. -/
def formalFirstVariation (x lambda : ℚ) : ℚ :=
  3 * x ^ 2 - 2 * lambda * x

/-- At `x=1`, the value equality `J=lambda A` holds with `lambda=1`. -/
theorem endpoint_value_equality :
    transfer 1 = 1 * budget 1 := by
  norm_num [transfer, budget]

/-- The corresponding first-variation coefficient is nonzero. -/
theorem endpoint_first_variation_nonzero :
    formalFirstVariation 1 1 = 1 := by
  norm_num [formalFirstVariation]

/-- Exact logical counterexample: pointwise value equality does not imply
stationarity of `J-lambda A`. -/
theorem value_equality_does_not_force_stationarity :
    ¬ (∀ x lambda : ℚ,
      transfer x = lambda * budget x →
      formalFirstVariation x lambda = 0) := by
  intro h
  have hbad := h 1 1 endpoint_value_equality
  norm_num [formalFirstVariation] at hbad

/-- Even an everywhere constant saturating sequence supplies no stationarity. -/
theorem constant_saturating_sequence_not_stationary :
    ∃ x : ℕ → ℚ,
      (∀ n, transfer (x n) = budget (x n)) ∧
      formalFirstVariation (x 0) 1 ≠ 0 := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro n
    norm_num [transfer, budget]
  · norm_num [formalFirstVariation]

/-- Cross-multiplied homogeneity identity: the cubic/quadratic quotient scales
linearly under amplitude scaling. -/
theorem amplitude_quotient_cross_identity (c x : ℚ) :
    transfer (c * x) * budget x =
      c * transfer x * budget (c * x) := by
  unfold transfer budget
  ring

/-- Along the unrestricted amplitude ray through `x=1`, the quotient at
amplitude `2` is strictly larger than at amplitude `1`, written without
division. -/
theorem unrestricted_amplitude_improves_quotient :
    transfer 2 * budget 1 > transfer 1 * budget 2 := by
  norm_num [transfer, budget]

/-- Scalar shadow of the constitutive relation `h=g^2`. -/
def Coupled (g h : ℚ) : Prop := h = g ^ 2

/-- The baseline pair satisfies the coupling. -/
theorem baseline_pair_is_coupled : Coupled 1 1 := by
  norm_num [Coupled]

/-- Independently scaling `g` while holding `h` fixed leaves the coupled
admissible set. -/
theorem independent_g_amplitude_breaks_coupling :
    ¬ Coupled 2 1 := by
  norm_num [Coupled]

/-- The exact pair of facts exposing the admissibility mismatch. -/
theorem independent_amplitude_curve_not_constraint_preserving :
    Coupled 1 1 ∧ ¬ Coupled 2 1 := by
  exact ⟨baseline_pair_is_coupled,
    independent_g_amplitude_breaks_coupling⟩

#print axioms endpoint_value_equality
#print axioms endpoint_first_variation_nonzero
#print axioms value_equality_does_not_force_stationarity
#print axioms constant_saturating_sequence_not_stationary
#print axioms amplitude_quotient_cross_identity
#print axioms unrestricted_amplitude_improves_quotient
#print axioms baseline_pair_is_coupled
#print axioms independent_g_amplitude_breaks_coupling
#print axioms independent_amplitude_curve_not_constraint_preserving

end Round211NavierStokes
end Millennium
