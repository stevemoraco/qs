import Mathlib

namespace Millennium.YangMills

/-!
# Uniform-domination convergence firewall

Finite/elementary real-analysis firewall for a load-bearing continuum-limit
inference. Uniform domination of a family by one summable/bounded majorant does
not, by itself, supply convergence of the dominated terms; pointwise convergence,
stabilization, Cauchy control, or a subsequence compactness theorem is still
required.

This file does not formalize Kirk v4's multiscale forest, distributional
compactness, Schwinger functions, Osterwalder--Schrader reconstruction, or a
Yang--Mills mass gap.
-/

/-- Elementary epsilon-tail convergence, kept explicit to avoid hiding the
logical issue behind filter notation. -/
def EpsilonConverges (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - L| < ε

/-- A uniformly bounded alternating sequence. -/
def alternating01 (n : ℕ) : ℝ :=
  if n % 2 = 0 then 0 else 1

/-- Every term is dominated by the same constant `1`. -/
theorem alternating01_uniformly_dominated (n : ℕ) :
    |alternating01 n| ≤ 1 := by
  unfold alternating01
  split <;> norm_num

/-- Even indices give the value `0`. -/
theorem alternating01_even (k : ℕ) :
    alternating01 (2 * k) = 0 := by
  unfold alternating01
  have h : (2 * k) % 2 = 0 := by omega
  simp [h]

/-- Odd indices give the value `1`. -/
theorem alternating01_odd (k : ℕ) :
    alternating01 (2 * k + 1) = 1 := by
  unfold alternating01
  have h : (2 * k + 1) % 2 ≠ 0 := by omega
  simp [h]

/-- The uniformly dominated alternating sequence has no real epsilon-tail
limit. This is the finite logical firewall against the inference
"uniform domination, hence termwise convergence". -/
theorem alternating01_no_limit (L : ℝ) :
    ¬ EpsilonConverges alternating01 L := by
  intro hconv
  rcases hconv (1 / 3 : ℝ) (by norm_num) with ⟨N, hN⟩
  have heven := hN (2 * N) (by omega)
  have hodd := hN (2 * N + 1) (by omega)
  rw [alternating01_even] at heven
  rw [alternating01_odd] at hodd
  rw [abs_lt] at heven hodd
  have hLlt : L < 1 / 3 := by linarith [heven.1]
  have hLgt : 2 / 3 < L := by linarith [hodd.2]
  linarith

/-- Uniform domination alone does not force convergence. -/
theorem uniform_domination_does_not_force_convergence :
    (∀ n : ℕ, |alternating01 n| ≤ 1) ∧
      (∀ L : ℝ, ¬ EpsilonConverges alternating01 L) := by
  exact ⟨alternating01_uniformly_dominated, alternating01_no_limit⟩

#print axioms alternating01_uniformly_dominated
#print axioms alternating01_even
#print axioms alternating01_odd
#print axioms alternating01_no_limit
#print axioms uniform_domination_does_not_force_convergence

end Millennium.YangMills
