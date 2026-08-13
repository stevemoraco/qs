import Mathlib

/-!
# Finite logical core of the flag/class-function obstruction

This file formalizes only the group-action identities saying that a conjugation-
invariant function is constant on a conjugacy orbit and therefore cannot
separate two points of that orbit. It does not formalize compact Lie groups,
Haar measure, Peter–Weyl theory, lattice gauge fields, OS reconstruction, or
the Yang–Mills problem.
-/

namespace YangMills
namespace FlagClassFunctionObstruction

variable {G α : Type*} [Group G]

/-- A conjugation-invariant scalar is constant along every conjugacy orbit. -/
theorem class_function_constant_on_orbit
    (F : G → α)
    (hF : ∀ g u : G, F (g * u * g⁻¹) = F u)
    (g u : G) :
    F (g * u * g⁻¹) = F u := by
  exact hF g u

/-- Two conjugate representatives cannot be separated by a class function. -/
theorem class_function_cannot_separate_conjugates
    (F : G → α)
    (hF : ∀ g u : G, F (g * u * g⁻¹) = F u)
    (g u v : G)
    (hv : v = g * u * g⁻¹) :
    F v = F u := by
  subst hv
  exact hF g u

/-- If a scalar changes along one conjugacy orbit, it is not conjugation
invariant. -/
theorem nonconstant_on_orbit_not_class_function
    (F : G → α) (g u : G)
    (hne : F (g * u * g⁻¹) ≠ F u) :
    ¬ (∀ h v : G, F (h * v * h⁻¹) = F v) := by
  intro hclass
  exact hne (hclass g u)

/-- A conjugation-invariant scalar has zero pairwise fluctuation on an orbit. -/
theorem orbit_difference_zero
    [Sub α] [Zero α]
    (F : G → α)
    (hF : ∀ g u : G, F (g * u * g⁻¹) = F u)
    (g u : G) :
    F (g * u * g⁻¹) - F u = 0 := by
  rw [hF]
  exact sub_self _

end FlagClassFunctionObstruction
end YangMills
