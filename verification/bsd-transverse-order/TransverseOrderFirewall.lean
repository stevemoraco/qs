import Mathlib

/-!
# BSD transverse-order firewall

Finite algebra only. This file formalizes the countermodel showing that complete
knowledge of one analytic fiber does not, by formal algebra alone, determine
vanishing order in an independent direction.

It does NOT prove or disprove BSD and makes no claim about actual L-functions.
-/

namespace Millennium.BSD.TransverseOrderFirewall

def twoParameterModel (m : ℕ) (s t : ℚ) : ℚ :=
  t + s ^ (m + 1)

theorem cyclotomic_fiber_independent (m : ℕ) (t : ℚ) :
    twoParameterModel m 0 t = t := by
  simp [twoParameterModel]

theorem transverse_fiber_power (m : ℕ) (s : ℚ) :
    twoParameterModel m s 0 = s ^ (m + 1) := by
  simp [twoParameterModel]

theorem same_fiber_arbitrary_transverse_power (m : ℕ) :
    ∃ F : ℚ → ℚ → ℚ,
      (∀ t : ℚ, F 0 t = t) ∧
      (∀ s : ℚ, F s 0 = s ^ (m + 1)) := by
  refine ⟨twoParameterModel m, ?_, ?_⟩
  · intro t
    exact cyclotomic_fiber_independent m t
  · intro s
    exact transverse_fiber_power m s

theorem same_cyclotomic_fiber (m n : ℕ) (t : ℚ) :
    twoParameterModel m 0 t = twoParameterModel n 0 t := by
  simp [twoParameterModel]

#print axioms cyclotomic_fiber_independent
#print axioms transverse_fiber_power
#print axioms same_fiber_arbitrary_transverse_power
#print axioms same_cyclotomic_fiber

end Millennium.BSD.TransverseOrderFirewall
