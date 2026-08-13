import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Tactic

/-!
# Rational checkpoint and bounded-window firewalls

These elementary theorems isolate two topology/quantifier arrows that arise in
continuous positivity criteria such as Suzuki's screw-function criterion for RH.
They do not define Suzuki's function and do not prove RH.
-/

open Set

/-- Nonnegativity of a continuous real-valued function on a dense set extends
to its whole domain. -/
theorem continuous_nonnegative_of_dense
    {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ}
    (hf : Continuous f) (hs : Dense s)
    (h_nonnegative : ∀ x ∈ s, 0 ≤ f x) :
    ∀ x, 0 ≤ f x := by
  have hsubset : s ⊆ {x | 0 ≤ f x} := by
    intro x hx
    exact h_nonnegative x hx
  have hclosed : IsClosed {x | 0 ≤ f x} :=
    isClosed_le continuous_const hf
  intro x
  apply closure_minimal hsubset hclosed
  rw [hs.closure_eq]
  exact mem_univ x

/-- For a continuous real function, checking nonnegativity at every rational
point is exactly equivalent to checking it at every real point. -/
theorem continuous_nonnegative_iff_rational
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∀ x : ℝ, 0 ≤ f x) ↔ (∀ q : ℚ, 0 ≤ f q) := by
  constructor
  · intro h q
    exact h q
  · intro h
    apply continuous_nonnegative_of_dense hf Rat.denseRange_cast
    rintro _ ⟨q, rfl⟩
    exact h q

/-- Strict positivity on a dense set does not extend to strict positivity at
limit points: `x ↦ x²` is positive off zero but vanishes at zero. -/
theorem strict_on_dense_does_not_force_strict_everywhere :
    Dense ({x : ℝ | x ≠ 0}) ∧
      (∀ x ∈ ({x : ℝ | x ≠ 0}), 0 < x ^ 2) ∧
      ¬ (∀ x : ℝ, 0 < x ^ 2) := by
  constructor
  · have hset :
        ({x : ℝ | x ≠ 0} : Set ℝ) = ({(0 : ℝ)} : Set ℝ)ᶜ := by
      ext x
      simp
    rw [hset]
    exact dense_compl_singleton (x := (0 : ℝ))
  constructor
  · intro x hx
    exact sq_pos_of_ne_zero hx
  · intro h
    simpa using h 0

/-- A positivity certificate on one bounded symmetric interval has no global
consequence without another theorem: `A²-x²` is nonnegative on `[-A,A]` and
negative at `A+1` when `A ≥ 0`. -/
theorem bounded_window_does_not_force_global (A : ℝ) (hA : 0 ≤ A) :
    (∀ x : ℝ, |x| ≤ A → 0 ≤ A ^ 2 - x ^ 2) ∧
      A ^ 2 - (A + 1) ^ 2 < 0 := by
  constructor
  · intro x hx
    have hxlo : -A ≤ x := neg_le_of_abs_le hx
    have hxhi : x ≤ A := le_of_abs_le hx
    have hprod : 0 ≤ (A - x) * (A + x) :=
      mul_nonneg (sub_nonneg.mpr hxhi) (by linarith)
    nlinarith [hprod]
  · nlinarith

#print axioms continuous_nonnegative_of_dense
#print axioms continuous_nonnegative_iff_rational
#print axioms strict_on_dense_does_not_force_strict_everywhere
#print axioms bounded_window_does_not_force_global
