import Mathlib

/-!
# Faizal–Shabir discrete two-loop invariant firewall

Finite telescoping algebra for the inverse-coupling center coordinate suggested by
arXiv:2606.19362v1 Section 10 after the one-loop normalization is repaired.

If a scalar center coordinate satisfies

  h_(n+1) = h_n + A + c_n + r_n,

then subtracting the one-loop drift `A*n` and the explicit accumulated correction
`sum c_j` leaves an invariant whose one-step change is exactly `r_n`.  In the
two-loop application one takes `c_n = B / h_n`.

This file does not prove the Yang–Mills recurrence, identify the two-loop coefficient,
prove summability of the post-two-loop residual, construct Lambda_YM, identify AF and
IR, prove a mass gap, or formalize continuum OS reconstruction.
-/

namespace Millennium.YangMills.FaizalShabirDiscreteTwoLoopInvariant

open scoped BigOperators

/-- The exact finite counterterm-subtracted coordinate. -/
def subtractedInvariant
    (h correction : ℕ → ℝ) (A : ℝ) (N : ℕ) : ℝ :=
  h N - A * (N : ℝ) - ∑ j in Finset.range N, correction j

/-- If the recurrence is `h_(n+1) = h_n + A + correction_n + residual_n`,
then the subtracted invariant changes by exactly the residual. -/
theorem subtractedInvariant_step
    (h correction residual : ℕ → ℝ)
    (A : ℝ) (n : ℕ)
    (hrec : h (n + 1) = h n + A + correction n + residual n) :
    subtractedInvariant h correction A (n + 1) -
        subtractedInvariant h correction A n = residual n := by
  simp [subtractedInvariant, Finset.sum_range_succ, hrec]
  ring

/-- Finite telescope: after subtracting the declared one-loop drift and correction
channel, the only accumulated change is the residual sum. -/
theorem subtractedInvariant_finite_telescope
    (h correction residual : ℕ → ℝ)
    (A : ℝ) (N : ℕ)
    (hrec : ∀ n, h (n + 1) = h n + A + correction n + residual n) :
    subtractedInvariant h correction A N =
      subtractedInvariant h correction A 0 +
        ∑ j in Finset.range N, residual j := by
  induction N with
  | zero => simp [subtractedInvariant]
  | succ n ih =>
      have hstep := subtractedInvariant_step h correction residual A n (hrec n)
      calc
        subtractedInvariant h correction A (n + 1) =
            subtractedInvariant h correction A n + residual n := by
              linarith
        _ = (subtractedInvariant h correction A 0 +
              ∑ j in Finset.range n, residual j) + residual n := by
              rw [ih]
        _ = subtractedInvariant h correction A 0 +
              ∑ j in Finset.range (n + 1), residual j := by
              rw [Finset.sum_range_succ]
              ring

/-- Exact two-loop specialization: the harmonic `B / h_n` channel is removed
from the residual rather than incorrectly being treated as absolutely summable. -/
theorem twoLoopDiscreteInvariant_step
    (h residual : ℕ → ℝ)
    (A B : ℝ) (n : ℕ)
    (hrec : h (n + 1) = h n + A + B / h n + residual n) :
    subtractedInvariant h (fun j => B / h j) A (n + 1) -
        subtractedInvariant h (fun j => B / h j) A n = residual n := by
  exact subtractedInvariant_step h (fun j => B / h j) residual A n hrec

/-- Two trajectories with the same declared one-loop and two-loop center
normalization differ, after subtraction, only by the difference of their residuals. -/
theorem twoTrajectoryInvariantDifference_step
    (h₁ h₂ r₁ r₂ : ℕ → ℝ)
    (A B : ℝ) (n : ℕ)
    (hrec₁ : h₁ (n + 1) = h₁ n + A + B / h₁ n + r₁ n)
    (hrec₂ : h₂ (n + 1) = h₂ n + A + B / h₂ n + r₂ n) :
    ((subtractedInvariant h₁ (fun j => B / h₁ j) A (n + 1) -
      subtractedInvariant h₂ (fun j => B / h₂ j) A (n + 1)) -
     (subtractedInvariant h₁ (fun j => B / h₁ j) A n -
      subtractedInvariant h₂ (fun j => B / h₂ j) A n)) =
      r₁ n - r₂ n := by
  have h₁step := twoLoopDiscreteInvariant_step h₁ r₁ A B n hrec₁
  have h₂step := twoLoopDiscreteInvariant_step h₂ r₂ A B n hrec₂
  linarith

#print axioms subtractedInvariant_step
#print axioms subtractedInvariant_finite_telescope
#print axioms twoLoopDiscreteInvariant_step
#print axioms twoTrajectoryInvariantDifference_step

end Millennium.YangMills.FaizalShabirDiscreteTwoLoopInvariant
