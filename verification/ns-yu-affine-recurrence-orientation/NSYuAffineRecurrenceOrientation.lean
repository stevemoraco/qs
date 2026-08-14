import Mathlib

/-!
# Navier–Stokes Yu affine recurrence / orientation firewalls

Finite scalar and finite-dimensional facts only.

These declarations do **not** formalize Yu's filtered Navier–Stokes estimates,
identify an actual exterior affine jet, prove recurrence of a PDE profile, or
prove Navier–Stokes regularity/blow-up.  They isolate two exact pieces used by
the accompanying source audit:

* geometric attenuation plus a bounded dyadic raw budget need not make a
  normalized affine coefficient decay;
* near-maximal work of a symmetric affine strain with a top spectral gap forces
  alignment with its top eigendirection.
-/

namespace NSYuAffineRecurrenceOrientation

def affineState (_ : Nat) : ℝ := 1

def affineInjection (_ : Nat) : ℝ := 3 / 4

theorem affine_plateau_step (n : Nat) :
    affineState (n + 1) =
      (1 / 4 : ℝ) * affineState n + affineInjection (n + 1) := by
  norm_num [affineState, affineInjection]

def rawBudget : Nat → ℝ
  | 0 => 0
  | n + 1 => rawBudget n + (1 / 2 : ℝ) ^ n

theorem rawBudget_closed (n : Nat) :
    rawBudget n = 2 * (1 - (1 / 2 : ℝ) ^ n) := by
  induction n with
  | zero => norm_num [rawBudget]
  | succ n ih =>
      rw [rawBudget, ih, pow_succ]
      ring

theorem rawBudget_le_two (n : Nat) : rawBudget n ≤ 2 := by
  rw [rawBudget_closed]
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  nlinarith

theorem affine_plateau_coexists_with_bounded_raw_budget (N : Nat) :
    (∀ n : Nat,
      affineState (n + 1) =
        (1 / 4 : ℝ) * affineState n + affineInjection (n + 1)) ∧
    rawBudget N ≤ 2 ∧
    affineState N = 1 := by
  exact ⟨affine_plateau_step, rawBudget_le_two N, rfl⟩

theorem diagonal_spectral_alignment_budget
    (lambda₁ lambda₂ lambda₃ x₁ x₂ x₃ epsilon gamma : ℝ)
    (horder : lambda₃ ≤ lambda₂)
    (hgap : gamma = lambda₁ - lambda₂)
    (hunit : x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 = 1)
    (hnear :
      lambda₁ -
          (lambda₁ * x₁ ^ 2 + lambda₂ * x₂ ^ 2 + lambda₃ * x₃ ^ 2)
        ≤ epsilon) :
    gamma * (x₂ ^ 2 + x₃ ^ 2) ≤ epsilon := by
  have hx₂ : 0 ≤ x₂ ^ 2 := sq_nonneg x₂
  have hx₃ : 0 ≤ x₃ ^ 2 := sq_nonneg x₃
  nlinarith

theorem diagonal_spectral_alignment_ratio
    (lambda₁ lambda₂ lambda₃ x₁ x₂ x₃ epsilon gamma : ℝ)
    (horder : lambda₃ ≤ lambda₂)
    (hgap : gamma = lambda₁ - lambda₂)
    (hgamma : 0 < gamma)
    (hunit : x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 = 1)
    (hnear :
      lambda₁ -
          (lambda₁ * x₁ ^ 2 + lambda₂ * x₂ ^ 2 + lambda₃ * x₃ ^ 2)
        ≤ epsilon) :
    x₂ ^ 2 + x₃ ^ 2 ≤ epsilon / gamma := by
  have hbudget : gamma * (x₂ ^ 2 + x₃ ^ 2) ≤ epsilon :=
    diagonal_spectral_alignment_budget
      lambda₁ lambda₂ lambda₃ x₁ x₂ x₃ epsilon gamma
      horder hgap hunit hnear
  apply (le_div_iff₀ hgamma).2
  nlinarith

theorem zero_top_gap_allows_no_first_axis_alignment :
    let lambda₁ : ℝ := 1
    let lambda₂ : ℝ := 1
    let lambda₃ : ℝ := -2
    let x₁ : ℝ := 0
    let x₂ : ℝ := 1
    let x₃ : ℝ := 0
    lambda₁ - lambda₂ = 0 ∧
    x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 = 1 ∧
    lambda₁ * x₁ ^ 2 + lambda₂ * x₂ ^ 2 + lambda₃ * x₃ ^ 2 = lambda₁ ∧
    x₂ ^ 2 + x₃ ^ 2 = 1 := by
  norm_num

#print axioms affine_plateau_step
#print axioms rawBudget_closed
#print axioms rawBudget_le_two
#print axioms affine_plateau_coexists_with_bounded_raw_budget
#print axioms diagonal_spectral_alignment_budget
#print axioms diagonal_spectral_alignment_ratio
#print axioms zero_top_gap_allows_no_first_axis_alignment

end NSYuAffineRecurrenceOrientation
