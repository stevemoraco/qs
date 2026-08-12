import Mathlib

/-!
# Yang–Mills: countable cylinder cores and the OS quotient

This file formalizes only finite/logical/scalar cores used in the accompanying
claimant/critic/rebuilder note.  It does not formalize probability spaces,
uncountable products, gauge fields, cylinder algebras, reflection positivity,
Osterwalder--Schrader reconstruction, Hamiltonians, Yang--Mills theory, or the
Clay theorem.
-/

namespace MillenniumRun17
namespace YMCountableOSCore

/-- Approximation in a stronger distance transfers to a pointwise dominated
weaker distance.  In the intended application, the stronger distance is the
Euclidean `L²` distance and the weaker one is the OS quotient distance. -/
theorem dominated_approximation
    {α ι : Type*}
    (dStrong dWeak : α → α → ℝ)
    (a : ι → α)
    (x : α)
    (hdom : ∀ i, dWeak x (a i) ≤ dStrong x (a i))
    (hdense : ∀ ε : ℝ, 0 < ε → ∃ i, dStrong x (a i) < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ i, dWeak x (a i) < ε := by
  intro ε hε
  obtain ⟨i, hi⟩ := hdense ε hε
  exact ⟨i, lt_of_le_of_lt (hdom i) hi⟩

/-- A contractive projection carries a dense approximating family to a dense
family in its fixed-point subspace.  Intended application: gauge averaging or
conditional expectation onto gauge-invariant observables. -/
theorem contractive_projection_approximation
    {α ι : Type*}
    (d : α → α → ℝ)
    (P : α → α)
    (a : ι → α)
    (x : α)
    (hfix : P x = x)
    (hcontract : ∀ y z, d (P y) (P z) ≤ d y z)
    (hdense : ∀ ε : ℝ, 0 < ε → ∃ i, d x (a i) < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ i, d x (P (a i)) < ε := by
  intro ε hε
  obtain ⟨i, hi⟩ := hdense ε hε
  refine ⟨i, ?_⟩
  have hle : d (P x) (P (a i)) ≤ d x (a i) := hcontract x (a i)
  simpa [hfix] using lt_of_le_of_lt hle hi

/-- The exact two-stage bridge used by the repaired route: first project to the
invariant subspace contractively in `L²`, then pass through a dominated OS
quotient seminorm. -/
theorem projected_dominated_approximation
    {α ι : Type*}
    (dL2 dOS : α → α → ℝ)
    (P : α → α)
    (a : ι → α)
    (x : α)
    (hfix : P x = x)
    (hcontract : ∀ y z, dL2 (P y) (P z) ≤ dL2 y z)
    (hdom : ∀ y, dOS x (P y) ≤ dL2 x (P y))
    (hdense : ∀ ε : ℝ, 0 < ε → ∃ i, dL2 x (a i) < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ i, dOS x (P (a i)) < ε := by
  intro ε hε
  obtain ⟨i, hi⟩ := hdense ε hε
  refine ⟨i, lt_of_le_of_lt (hdom (a i)) ?_⟩
  have hle : dL2 (P x) (P (a i)) ≤ dL2 x (a i) :=
    hcontract x (a i)
  simpa [hfix] using lt_of_le_of_lt hle hi

/-- Scalar Cauchy--Schwarz firewall: if two nonnegative seminorms satisfy the
corresponding squared inequality, then the first is dominated by the second. -/
theorem nonnegative_norm_of_sq_le_sq
    (os l2 : ℝ)
    (hos : 0 ≤ os)
    (hl2 : 0 ≤ l2)
    (hSq : os ^ 2 ≤ l2 ^ 2) :
    os ≤ l2 := by
  nlinarith

/-- Exact fiber identity behind the hidden-coordinate countermodel.  A predictor
which does not see a fair sign incurs mean squared error `1 + y²` on the two
possible values of that sign. -/
theorem hidden_coordinate_pair_identity (y : ℝ) :
    ((1 - y) ^ 2 + ((-1 : ℝ) - y) ^ 2) / 2 = 1 + y ^ 2 := by
  ring

/-- Consequently every predictor independent of the hidden fair sign has
conditional mean squared error at least one. -/
theorem hidden_coordinate_pair_floor (y : ℝ) :
    1 ≤ ((1 - y) ^ 2 + ((-1 : ℝ) - y) ^ 2) / 2 := by
  rw [hidden_coordinate_pair_identity]
  exact le_add_of_nonneg_right (sq_nonneg y)

/-- No such hidden-coordinate predictor can achieve an error threshold strictly
below one. -/
theorem hidden_coordinate_no_subunit_error
    (y ε : ℝ)
    (hε : ε < 1) :
    ¬ (((1 - y) ^ 2 + ((-1 : ℝ) - y) ^ 2) / 2 < ε) := by
  intro h
  have hfloor := hidden_coordinate_pair_floor y
  linarith

#print axioms dominated_approximation
#print axioms contractive_projection_approximation
#print axioms projected_dominated_approximation
#print axioms nonnegative_norm_of_sq_le_sq
#print axioms hidden_coordinate_pair_identity
#print axioms hidden_coordinate_pair_floor
#print axioms hidden_coordinate_no_subunit_error

end YMCountableOSCore
end MillenniumRun17
