import Mathlib

/-!
# Restriction recovery for phase embeddings

The Fourier-flat construction used in `FOURIER_ENTROPY_BARRIER.md` has the form

  `(x,y) ↦ phase x y XOR g y`.

Whenever one distinguished `x₀` makes `phase x₀ y = false` for every `y`, fixing
`x=x₀` recovers the arbitrary function `g`. This file formalizes that logical
core independently of the separate Walsh-transform calculation.
-/

namespace PvsNP.FourierPhaseEmbedding

variable {X Y : Type*}

/-- Embed an arbitrary function `g` into the phase of a two-block function. -/
def phaseEmbed (phase : X → Y → Bool) (g : Y → Bool) : X → Y → Bool :=
  fun x y => xor (phase x y) (g y)

/-- A zero-phase slice recovers the embedded function exactly. -/
theorem recover_on_zero_phase
    (phase : X → Y → Bool) (g : Y → Bool) (x₀ : X)
    (hZero : ∀ y : Y, phase x₀ y = false) :
    ∀ y : Y, phaseEmbed phase g x₀ y = g y := by
  intro y
  simp [phaseEmbed, hZero y]

/-- The phase embedding is injective whenever a zero-phase slice exists. -/
theorem phaseEmbed_injective
    (phase : X → Y → Bool) (x₀ : X)
    (hZero : ∀ y : Y, phase x₀ y = false) :
    Function.Injective (phaseEmbed phase) := by
  intro g h hEq
  funext y
  have hSlice := congrFun (congrFun hEq x₀) y
  simpa [phaseEmbed, hZero y] using hSlice

/-- Equality of embedded functions can be tested on the zero-phase slice. -/
theorem phaseEmbed_eq_iff
    (phase : X → Y → Bool) (x₀ : X)
    (hZero : ∀ y : Y, phase x₀ y = false)
    (g h : Y → Bool) :
    phaseEmbed phase g = phaseEmbed phase h ↔ g = h := by
  constructor
  · exact phaseEmbed_injective phase x₀ hZero
  · intro hgh
    simpa [hgh]

end PvsNP.FourierPhaseEmbedding
