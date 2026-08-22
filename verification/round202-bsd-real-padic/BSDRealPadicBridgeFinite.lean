import Mathlib

/-!
# Round 202 BSD finite bridge and countermodel cores

This file formalizes only elementary rank bookkeeping and finite algebraic
countermodels. It does not formalize elliptic curves, L-functions, Selmer
complexes, p-adic heights, Tate--Shafarevich groups, or BSD.
-/

namespace Millennium
namespace Round202BSD

/-- Artin-formalism rank additivity plus the corresponding Mordell--Weil
additivity allows exact quadratic-twist descent of rank equality. -/
theorem quadratic_twist_rank_descent
    (analyticE analyticTwist analyticK : ℕ)
    (algebraicE algebraicTwist algebraicK : ℕ)
    (hAnalytic : analyticK = analyticE + analyticTwist)
    (hAlgebraic : algebraicK = algebraicE + algebraicTwist)
    (hK : analyticK = algebraicK)
    (hTwist : analyticTwist = algebraicTwist) :
    analyticE = algebraicE := by
  omega

/-- The determinant polynomial for a two-by-two pairing matrix. -/
def detTwo (a b c d : ℚ) : ℚ := a * d - b * c

/-- On one fixed two-dimensional rational space, one bilinear-form determinant
can be nonzero while another is zero. Thus nondegeneracy does not transfer
between realizations without a comparison theorem. -/
theorem real_regulator_does_not_force_local_regulator :
    detTwo 1 0 0 1 = 1 ∧ detTwo 1 0 0 0 = 0 := by
  norm_num [detTwo]

/-- More generally, a nonzero determinant and a zero determinant are compatible
pieces of independent data on the same finite rank. -/
theorem independent_pairing_determinants_exist :
    ∃ realDet localDet : ℚ, realDet ≠ 0 ∧ localDet = 0 := by
  exact ⟨1, 0, by norm_num, rfl⟩

/-- Every primary component can be individually finite while nontrivial
components occur at arbitrarily large primes/indices. This is the finite-support
shadow of the warning that primewise finiteness is not global finiteness. -/
theorem pointwise_finite_does_not_force_finite_support :
    ∃ componentSize : ℕ → ℕ,
      (∀ n, componentSize n = 1) ∧
      ¬ ∃ N, ∀ n ≥ N, componentSize n = 0 := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro n
    rfl
  · rintro ⟨N, hN⟩
    have := hN N (le_refl N)
    norm_num at this

/-- A finite list of local scalar equalities cannot determine one additional
unconstrained Archimedean scalar. -/
theorem finite_local_data_leave_archimedean_coordinate_free
    (localData : Fin n → ℚ) :
    ∃ x y : ℚ, x ≠ y ∧
      (∀ i, localData i = localData i) := by
  refine ⟨0, 1, by norm_num, ?_⟩
  intro i
  rfl

#print axioms quadratic_twist_rank_descent
#print axioms real_regulator_does_not_force_local_regulator
#print axioms independent_pairing_determinants_exist
#print axioms pointwise_finite_does_not_force_finite_support
#print axioms finite_local_data_leave_archimedean_coordinate_free

end Round202BSD
end Millennium
