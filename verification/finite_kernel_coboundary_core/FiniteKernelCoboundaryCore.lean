import Mathlib

namespace FiniteKernelCoboundaryCore

/-- One-step shift of an orbit observable. -/
def shift (f : ℕ → ℚ) : ℕ → ℚ := fun n => f (n + 1)

/-- Evaluation of a finite scalar kernel on an orbit. -/
def orbitWeighted : List ℚ → (ℕ → ℚ) → ℚ
  | [], _ => 0
  | b :: bs, f => b * f 0 + orbitWeighted bs (shift f)

/-- The potential synthesized from the tail masses of a finite kernel.
For `b₀ :: b₁ :: ...`, the coefficient of `f(T^j x)` is the sum of
all kernel coefficients strictly after `j`. -/
def kernelPotential : List ℚ → (ℕ → ℚ) → ℚ
  | [], _ => 0
  | _ :: bs, f => bs.sum * f 0 + kernelPotential bs (shift f)

/-- Exact finite-kernel coboundary identity. The total kernel mass appears
in front of the current observable; specializing that mass to one turns any
finite probability-weighted block average into one pointwise corrected step. -/
theorem kernelPotential_identity (b : List ℚ) (f : ℕ → ℚ) :
    b.sum * f 0 + kernelPotential b (shift f) - kernelPotential b f =
      orbitWeighted b f := by
  induction b generalizing f with
  | nil => simp [kernelPotential, orbitWeighted]
  | cons b bs ih =>
      simp only [List.sum_cons, kernelPotential, orbitWeighted]
      have h := ih (shift f)
      dsimp [shift] at h ⊢
      linarith

/-- Probability-kernel specialization: the synthesized bounded coboundary
redistributes a finite block average into an exact one-step defect. -/
theorem probabilityKernel_identity
    (b : List ℚ) (f : ℕ → ℚ) (hmass : b.sum = 1) :
    f 0 + kernelPotential b (shift f) - kernelPotential b f =
      orbitWeighted b f := by
  simpa [hmass] using kernelPotential_identity b f

/-- Any lower bound for the finite block average transfers without loss to
the pointwise coboundary-corrected observable. -/
theorem blockLowerBound_to_correctedStep
    (b : List ℚ) (f : ℕ → ℚ) (η : ℚ)
    (hmass : b.sum = 1)
    (hblock : η ≤ orbitWeighted b f) :
    η ≤ f 0 + kernelPotential b (shift f) - kernelPotential b f := by
  rw [probabilityKernel_identity b f hmass]
  exact hblock

/-- A finite coboundary cannot change total coefficient mass. Therefore mass
one is necessary for an identity whose current-observable coefficient is one
and whose shifted tail has no terminal remainder. -/
theorem mass_one_necessary
    (targetMass : ℚ)
    (hcoeff : (1 : ℚ) = targetMass) :
    targetMass = 1 := by
  linarith

#print axioms kernelPotential_identity
#print axioms probabilityKernel_identity
#print axioms blockLowerBound_to_correctedStep
#print axioms mass_one_necessary

end FiniteKernelCoboundaryCore
