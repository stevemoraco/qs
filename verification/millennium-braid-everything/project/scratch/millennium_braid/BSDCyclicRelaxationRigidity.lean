import Mathlib

/-!
# BSD cyclic-relaxation parity core

Finite combinatorial core of the cyclic-relaxation/self-dual rigidity theorem.
This file does NOT prove BSD.  The arithmetic input, proved separately over a DVR,
is that a cyclic quotient forces each depth-profile increment to be either 0 or 1.
If both endpoint profiles are symplectic/self-dual, every depth multiplicity is even,
so every such binary increment must vanish.
-/

namespace BSDBraid

/-- Two even natural numbers cannot differ by exactly one. -/
theorem even_binary_step_eq
    (a b : ℕ)
    (ha : Even a)
    (hb : Even b)
    (hstep : b = a ∨ b = a + 1) :
    b = a := by
  rcases hstep with h | h
  · exact h
  · rcases ha with ⟨x, hx⟩
    rcases hb with ⟨y, hy⟩
    omega

/--
Pointwise rigidity: a binary interlacing perturbation between two even-valued
profiles is identically zero.
-/
theorem selfDual_binary_interlace_rigidity
    {ι : Type*}
    (tauA tauB : ι → ℕ)
    (hA : ∀ i, Even (tauA i))
    (hB : ∀ i, Even (tauB i))
    (hstep : ∀ i, tauB i = tauA i ∨ tauB i = tauA i + 1) :
    tauB = tauA := by
  funext i
  exact even_binary_step_eq (tauA i) (tauB i) (hA i) (hB i) (hstep i)

/--
Finite-profile form suitable for Smith/Bockstein depth vectors indexed by `Fin n`.
-/
theorem selfDual_binary_interlace_fin
    (n : ℕ)
    (tauA tauB : Fin n → ℕ)
    (hA : ∀ i, Even (tauA i))
    (hB : ∀ i, Even (tauB i))
    (hstep : ∀ i, tauB i = tauA i ∨ tauB i = tauA i + 1) :
    tauB = tauA := by
  exact selfDual_binary_interlace_rigidity tauA tauB hA hB hstep

end BSDBraid
