import BSDGVSemiprimeDensity

/-!
# Abstract asymptotic aggregation for the BSD semiprime state space

This file formalizes the finite-to-asymptotic algebra after an external
analytic theorem has supplied statewise equidistribution. It makes no claim
that the quadratic large sieve or the prime number theorem is formalized here.
-/

open Filter Topology

namespace BSDGVSemiprimeDensity

set_option maxRecDepth 100000

def acceptedStates : Finset State :=
  allStates.filter fun x => accepts x.1 x.2.1 x.2.2 = true

/-- The accepted-state finset has cardinality 28. -/
theorem acceptedStates_card_eq : acceptedStates.card = 28 := by
  simpa [acceptedStates, acceptedStateCount] using acceptedStateCount_eq

/-- Exact finite aggregation: if every residue/sign state has the same real
mass `c`, then the accepted states have total mass `28 * c`. -/
theorem accepted_uniform_mass
    (mass : State → ℝ) (c : ℝ)
    (h : ∀ x, mass x = c) :
    (∑ x ∈ acceptedStates, mass x) = 28 * c := by
  calc
    (∑ x ∈ acceptedStates, mass x) = ∑ _x ∈ acceptedStates, c := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact h x
    _ = acceptedStates.card * c := by simp
    _ = 28 * c := by rw [acceptedStates_card_eq]

/-- Statewise convergence to a common mass `c` forces the accepted-state total
to converge to `28 * c`. This is the exact finite-to-asymptotic algebra used
after the analytic equidistribution theorem. -/
theorem accepted_mass_tendsto
    (mass : State → ℕ → ℝ) (c : ℝ)
    (h : ∀ x, Tendsto (mass x) atTop (𝓝 c)) :
    Tendsto
      (fun n => ∑ x ∈ acceptedStates, mass x n)
      atTop (𝓝 (28 * c)) := by
  have hsum :
      Tendsto
        (fun n => ∑ x ∈ acceptedStates, mass x n)
        atTop
        (𝓝 (∑ _x ∈ acceptedStates, c)) := by
    exact tendsto_finset_sum acceptedStates (fun x _hx => h x)
  have hconst : (∑ _x ∈ acceptedStates, c) = 28 * c := by
    exact accepted_uniform_mass (fun _x => c) c (fun _x => rfl)
  rw [hconst] at hsum
  exact hsum

/-- In particular, if every one of the 128 states has limiting mass `1/128`,
the accepted states have limiting mass `7/32`. -/
theorem accepted_density_tendsto
    (mass : State → ℕ → ℝ)
    (h : ∀ x, Tendsto (mass x) atTop (𝓝 (1 / 128 : ℝ))) :
    Tendsto
      (fun n => ∑ x ∈ acceptedStates, mass x n)
      atTop (𝓝 (7 / 32 : ℝ)) := by
  convert accepted_mass_tendsto mass (1 / 128 : ℝ) h using 1 <;> norm_num

#print axioms acceptedStates_card_eq
#print axioms accepted_uniform_mass
#print axioms accepted_mass_tendsto
#print axioms accepted_density_tendsto

end BSDGVSemiprimeDensity
