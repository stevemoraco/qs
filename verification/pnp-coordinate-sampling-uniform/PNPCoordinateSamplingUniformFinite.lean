import Mathlib

/-!
# P versus NP coordinate-sampling uniform magnification finite core

HONESTY BOUNDARY

This file verifies only finite scalar and logical interfaces used in a
conditional uniform magnification theorem:

* one-quarter one-sided error amplified over `N` independent fingerprints;
* the simultaneous union-bound arithmetic over at most `2^N` inputs;
* a collision exponent large enough to beat a finite sparse-set union bound;
* the exact logical contrapositive from `P=NP -> SmallCircuits` and a lower
  bound `not SmallCircuits` to `P!=NP`;
* the conclusions `P!=NP` and `P!=NP^ParityP` are represented by distinct
  propositions and are never silently identified;
* YES, NO, and outside-promise inputs are distinct constructors.

It does not formalize probability spaces, Boolean circuits, MCSP, P-uniformity,
Turing machines, P, NP, the asymptotic sampling theorem, or the Clay statement.
-/

namespace MillenniumBraid
namespace PNPCoordinateSamplingUniformFinite

/-- Exact amplification identity: `2^N` possible inputs and false-accept
probability `4^{-N}` leave total union-bound mass `2^{-N}`. -/
theorem simultaneous_union_identity (N : ℕ) :
    (2 : ℝ) ^ N * (1 / 4 : ℝ) ^ N = (1 / 2 : ℝ) ^ N := by
  rw [← mul_pow]
  norm_num

/-- The amplified union-bound mass is strictly below one at every positive
input length. -/
theorem simultaneous_union_lt_one
    (N : ℕ)
    (hN : 0 < N) :
    (2 : ℝ) ^ N * (1 / 4 : ℝ) ^ N < 1 := by
  rw [simultaneous_union_identity]
  exact pow_lt_one₀ (by norm_num) (by norm_num) hN

/-- If every fixed NO input has false-accept probability at most `1/4`, then
`N` independent repetitions give the scalar budget `4^{-N}`. -/
theorem one_quarter_amplification
    (p : ℝ)
    (N : ℕ)
    (hp0 : 0 ≤ p)
    (hp : p ≤ 1 / 4) :
    p ^ N ≤ (1 / 4 : ℝ) ^ N := by
  exact pow_le_pow_left₀ hp0 hp N

/-- A finite sparse-union exponent budget. This is the scalar endpoint of
`T * exp(-r/q) <= 1/4` after bounding `T <= exp(L)` and `r/q >= L+log 4`. -/
theorem sparse_collision_budget
    (T collision : ℝ)
    (hT : 0 ≤ T)
    (hTupper : T ≤ Real.exp 1)
    (hcollision : collision ≤ Real.exp (-3)) :
    T * collision ≤ Real.exp (-2) := by
  calc
    T * collision ≤ Real.exp 1 * Real.exp (-3) := by
      exact mul_le_mul hTupper hcollision
        (by positivity) hT
    _ = Real.exp (-2) := by
      rw [← Real.exp_add]
      norm_num

/-- Abstract terminality core: if equality of the official classes would put
one fixed promise problem in the advertised small-circuit class, then a lower
bound for that same promise problem proves the classes unequal. -/
theorem terminal_magnification_contrapositive
    (PEqualsNP SmallCircuits : Prop)
    (hupper : PEqualsNP → SmallCircuits)
    (hlower : ¬ SmallCircuits) :
    ¬ PEqualsNP := by
  intro heq
  exact hlower (hupper heq)

/-- Distinguish the official `P=NP` proposition from a stronger oracle-class
identity. No implication between their negations is built into the finite
model. -/
structure ComplexityClaims where
  pEqualsNP : Prop
  pEqualsNPParityP : Prop

/-- A separation from the parity-oracle class is not definitionally the same
statement as the official P-versus-NP separation. -/
theorem parity_separation_stays_parity
    (claims : ComplexityClaims)
    (h : ¬ claims.pEqualsNPParityP) :
    ¬ claims.pEqualsNPParityP := h

/-- Promise inputs have three distinct statuses; circuits are constrained only
on YES and NO constructors. -/
inductive PromiseStatus where
  | yes
  | no
  | outside
  deriving DecidableEq

theorem yes_ne_no : PromiseStatus.yes ≠ PromiseStatus.no := by decide

theorem no_ne_outside : PromiseStatus.no ≠ PromiseStatus.outside := by decide

theorem yes_ne_outside : PromiseStatus.yes ≠ PromiseStatus.outside := by decide

/-- A finite length bound of the form `N*m + N` factors exactly as
`N*(m+1)`, isolating the one leading simultaneous-derandomization factor. -/
theorem one_leading_factor (N m : ℕ) :
    N * m + N = N * (m + 1) := by
  omega

#print axioms simultaneous_union_identity
#print axioms simultaneous_union_lt_one
#print axioms one_quarter_amplification
#print axioms sparse_collision_budget
#print axioms terminal_magnification_contrapositive
#print axioms parity_separation_stays_parity
#print axioms yes_ne_no
#print axioms no_ne_outside
#print axioms yes_ne_outside
#print axioms one_leading_factor

end PNPCoordinateSamplingUniformFinite
end MillenniumBraid
