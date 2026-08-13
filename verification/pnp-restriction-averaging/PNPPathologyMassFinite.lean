import Mathlib

open scoped BigOperators

namespace MillenniumBraid
namespace PNPPathologyMassFinite

variable {C X : Type*} [Fintype C] [Fintype X]

def mixedError (mu : C → ℝ) (err : C → X → ℝ) (x : X) : ℝ :=
  ∑ c, mu c * err c x

def subfamilyMass (mu : C → ℝ) (p : C → Prop) [DecidablePred p] : ℝ :=
  ∑ c, if p c then mu c else 0

end PNPPathologyMassFinite
end MillenniumBraid
