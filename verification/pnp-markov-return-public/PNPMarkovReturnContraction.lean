import Mathlib

/-!
# P versus NP: Markov return-contraction core

This file formalizes the functional-analytic core of the independent proof that
odd-time weight-one return probabilities for the random walk used in the
full-cube parity compressor are nonincreasing.

The proved statement is deliberately typed at its exact scope:

* `T` is any norm contraction on a seminormed additive commutative group;
* `returnEnergy T x m = ‖T^m x‖²`, with the orbit written recursively;
* return energy decreases at every step and after every finite number of steps;
* any nonnegative scalar multiple of that energy has the same monotonicity;
* any odd-indexed probability sequence represented by such a scaled energy is
  bounded by its value at index three.

This file does **not** formalize the hypercube Markov operator, the identity
between its return probability and the squared `L²` norm, Boolean circuit
semantics, hardness magnification, or `P ≠ NP`.  Those are separate bridges.
-/

namespace PNP
namespace MarkovReturnContraction

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The recursively generated orbit `x, T x, T (T x), ...`. -/
def orbit (T : E → E) (x : E) : ℕ → E
  | 0 => x
  | n + 1 => T (orbit T x n)

/-- Squared norm of the `m`-th point of an orbit. -/
def returnEnergy (T : E → E) (x : E) (m : ℕ) : ℝ :=
  ‖orbit T x m‖ ^ 2

/-- Squaring preserves an inequality between nonnegative norms. -/
theorem norm_sq_le_norm_sq {x y : E} (hxy : ‖x‖ ≤ ‖y‖) :
    ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  nlinarith [norm_nonneg x, norm_nonneg y]

/-- A norm contraction makes return energy decrease by one step. -/
theorem returnEnergy_succ_le
    (T : E → E) (hT : ∀ y, ‖T y‖ ≤ ‖y‖) (x : E) (m : ℕ) :
    returnEnergy T x (Nat.succ m) ≤ returnEnergy T x m := by
  change ‖T (orbit T x m)‖ ^ 2 ≤ ‖orbit T x m‖ ^ 2
  exact norm_sq_le_norm_sq (hT (orbit T x m))

/-- A norm contraction makes return energy decrease after any finite number of
additional steps. -/
theorem returnEnergy_add_le
    (T : E → E) (hT : ∀ y, ‖T y‖ ≤ ‖y‖) (x : E) (m d : ℕ) :
    returnEnergy T x (m + d) ≤ returnEnergy T x m := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ]
      exact le_trans (returnEnergy_succ_le T hT x (m + d)) ih

/-- A nonnegative scalar multiple of return energy. -/
def scaledReturn (c : ℝ) (T : E → E) (x : E) (m : ℕ) : ℝ :=
  c * returnEnergy T x m

/-- Nonnegative scaling preserves one-step return monotonicity. -/
theorem scaledReturn_succ_le
    (c : ℝ) (hc : 0 ≤ c)
    (T : E → E) (hT : ∀ y, ‖T y‖ ≤ ‖y‖) (x : E) (m : ℕ) :
    scaledReturn c T x (Nat.succ m) ≤ scaledReturn c T x m := by
  exact mul_le_mul_of_nonneg_left (returnEnergy_succ_le T hT x m) hc

/-- Nonnegative scaling preserves every finite-step return inequality. -/
theorem scaledReturn_add_le
    (c : ℝ) (hc : 0 ≤ c)
    (T : E → E) (hT : ∀ y, ‖T y‖ ≤ ‖y‖) (x : E) (m d : ℕ) :
    scaledReturn c T x (m + d) ≤ scaledReturn c T x m := by
  exact mul_le_mul_of_nonneg_left (returnEnergy_add_le T hT x m d) hc

/-- If the odd-indexed values of `p` are represented by scaled return energy,
then consecutive odd values decrease. -/
theorem represented_odd_probability_succ_le
    (p : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (T : E → E) (hT : ∀ y, ‖T y‖ ≤ ‖y‖) (x : E)
    (hrep : ∀ m, p (2 * m + 1) = scaledReturn c T x m)
    (m : ℕ) :
    p (2 * Nat.succ m + 1) ≤ p (2 * m + 1) := by
  rw [hrep (Nat.succ m), hrep m]
  exact scaledReturn_succ_le c hc T hT x m

/-- Every represented odd value from index three onward is at most the value
at index three.  Writing the index as `2 * (1 + d) + 1` keeps every quantifier
and parity condition explicit. -/
theorem represented_odd_probability_le_three
    (p : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (T : E → E) (hT : ∀ y, ‖T y‖ ≤ ‖y‖) (x : E)
    (hrep : ∀ m, p (2 * m + 1) = scaledReturn c T x m)
    (d : ℕ) :
    p (2 * (1 + d) + 1) ≤ p 3 := by
  rw [hrep (1 + d)]
  have hp3 : p 3 = scaledReturn c T x 1 := by
    simpa using hrep 1
  rw [hp3]
  exact scaledReturn_add_le c hc T hT x 1 d

#print axioms norm_sq_le_norm_sq
#print axioms returnEnergy_succ_le
#print axioms returnEnergy_add_le
#print axioms scaledReturn_succ_le
#print axioms scaledReturn_add_le
#print axioms represented_odd_probability_succ_le
#print axioms represented_odd_probability_le_three

end MarkovReturnContraction
end PNP
