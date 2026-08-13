import Mathlib

namespace NavierStokesQuotientStationarityCountermodel

/-- A toy visibility with the same quadratic amplitude homogeneity used in
the endpoint quotient argument. -/
def visibility (a : ℝ) : ℝ := a ^ 2

/-- A toy transfer with the same cubic amplitude homogeneity. -/
def transfer (a : ℝ) : ℝ := a ^ 3

/-- A deliberately constrained admissible class. It models an endpoint
class inherited from a PDE extraction when no closure under ambient
amplitude variations has been proved. -/
def admissible (a : ℝ) : Prop := a = 1

/-- Maximization on a constrained class does not license the ambient Euler
identity. Here `a = 1` is the global maximizer of `transfer / visibility`
on the entire admissible class, and it saturates its quotient value, but the
homogeneity identity `3 J = 2 Λ A` is false.

This is the finite logical firewall for differentiating an amplitude curve
that has not been shown to remain in the admissible PDE-realizable class. -/
theorem constrainedQuotientMaximumDoesNotGiveAmbientEulerIdentity :
    let Λ := transfer 1 / visibility 1
    (∀ a : ℝ, admissible a → transfer a / visibility a ≤ Λ) ∧
    transfer 1 = Λ * visibility 1 ∧
    3 * transfer 1 ≠ 2 * Λ * visibility 1 := by
  dsimp [admissible, transfer, visibility]
  constructor
  · intro a ha
    subst a
    norm_num
  · norm_num

/-- Even without constraints, the pointwise equality `J = Λ A` is only the
definition of a quotient value. It does not imply the Euler homogeneity
identity used by the strictness argument. -/
theorem quotientEqualityAloneDoesNotGiveEulerIdentity :
    ∃ A J Λ : ℝ,
      0 < A ∧
      J = Λ * A ∧
      3 * J ≠ 2 * Λ * A := by
  exact ⟨1, 1, 1, by norm_num⟩

/-- A one-point discrete analogue of a localized Dirichlet contribution
after the mass-preserving change of variables. The factor `s^2` is the
unlocalized derivative scaling, while `cutoff (1/s)` records that a fixed
physical cutoff becomes `χ(Z/s)` in the rescaled coordinates. -/
def cutoff (x : ℝ) : ℝ := x

noncomputable def fixedCutoffScaledVisibility (s : ℝ) : ℝ :=
  s ^ 2 * cutoff (1 / s) ^ 2

/-- Keeping a nonconstant cutoff fixed destroys exact degree-two
homogeneity. At scale two the transformed localized contribution equals
one, while multiplying its scale-one value by `2^2` gives four.

This is the finite algebraic firewall for the unsupported replacement of
`χ(Z/s)` by `χ(Z)` in a localized dilation identity. -/
theorem fixedCutoffBreaksDegreeTwoHomogeneity :
    fixedCutoffScaledVisibility 2 ≠
      2 ^ 2 * fixedCutoffScaledVisibility 1 := by
  norm_num [fixedCutoffScaledVisibility, cutoff]

#print axioms constrainedQuotientMaximumDoesNotGiveAmbientEulerIdentity
#print axioms quotientEqualityAloneDoesNotGiveEulerIdentity
#print axioms fixedCutoffBreaksDegreeTwoHomogeneity

end NavierStokesQuotientStationarityCountermodel
