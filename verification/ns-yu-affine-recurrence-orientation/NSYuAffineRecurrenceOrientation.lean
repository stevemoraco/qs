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

noncomputable section

/-- A normalized affine coefficient plateau. -/
def affineState (_ : Nat) : ℝ := 1

/-- The fresh-annulus injection that exactly sustains the plateau against a
quarter-strength inherited coefficient. -/
def affineInjection (_ : Nat) : ℝ := 3 / 4

/-- A constant normalized affine plateau is exactly compatible with the abstract
quarter-memory recurrence `c_{n+1} = c_n/4 + b_{n+1}`. -/
theorem affine_plateau_step (n : Nat) :
    affineState (n + 1) =
      (1 / 4 : ℝ) * affineState n + affineInjection (n + 1) := by
  norm_num [affineState, affineInjection]

/-- Finite dyadic raw-energy budget used only as a hostile scalar model. -/
def rawBudget : Nat → ℝ
  | 0 => 0
  | n + 1 => rawBudget n + (1 / 2 : ℝ) ^ n

/-- Closed form of the finite dyadic budget. -/
theorem rawBudget_closed (n : Nat) :
    rawBudget n = 2 * (1 - (1 / 2 : ℝ) ^ n) := by
  induction n with
  | zero => norm_num [rawBudget]
  | succ n ih =>
      rw [rawBudget, ih, pow_succ]
      ring

/-- Every finite dyadic raw budget is bounded by two. -/
theorem rawBudget_le_two (n : Nat) : rawBudget n ≤ 2 := by
  rw [rawBudget_closed]
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  nlinarith

/-- The normalized affine plateau can coexist, for every finite depth, with a
uniformly bounded dyadic raw budget.  This is a finite no-free-lunch firewall:
it does not assert that a Navier–Stokes solution realizes the model. -/
theorem affine_plateau_coexists_with_bounded_raw_budget (N : Nat) :
    (∀ n : Nat,
      affineState (n + 1) =
        (1 / 4 : ℝ) * affineState n + affineInjection (n + 1)) ∧
    rawBudget N ≤ 2 ∧
    affineState N = 1 := by
  exact ⟨affine_plateau_step, rawBudget_le_two N, rfl⟩

/-- Quantitative spectral-alignment inequality for a diagonal symmetric strain.
If `lambda₃ ≤ lambda₂`, `gamma = lambda₁-lambda₂`, `x` is unit length, and the
Rayleigh quotient is within `epsilon` of `lambda₁`, then the squared mass away
from the first eigendirection costs at least `gamma`. -/
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
  have hid :
      lambda₁ -
          (lambda₁ * x₁ ^ 2 + lambda₂ * x₂ ^ 2 + lambda₃ * x₃ ^ 2) =
        (lambda₁ - lambda₂) * x₂ ^ 2 +
          (lambda₁ - lambda₃) * x₃ ^ 2 := by
    linear_combination -lambda₁ * hunit
  have h13 : gamma ≤ lambda₁ - lambda₃ := by
    rw [hgap]
    linarith
  have hmul : gamma * x₃ ^ 2 ≤ (lambda₁ - lambda₃) * x₃ ^ 2 :=
    mul_le_mul_of_nonneg_right h13 (sq_nonneg x₃)
  calc
    gamma * (x₂ ^ 2 + x₃ ^ 2) =
        gamma * x₂ ^ 2 + gamma * x₃ ^ 2 := by ring
    _ ≤ gamma * x₂ ^ 2 + (lambda₁ - lambda₃) * x₃ ^ 2 :=
      add_le_add (le_refl _) hmul
    _ = (lambda₁ - lambda₂) * x₂ ^ 2 +
          (lambda₁ - lambda₃) * x₃ ^ 2 := by rw [hgap]
    _ = lambda₁ -
          (lambda₁ * x₁ ^ 2 + lambda₂ * x₂ ^ 2 + lambda₃ * x₃ ^ 2) :=
      hid.symm
    _ ≤ epsilon := hnear

/-- With a strictly positive top eigengap, near-maximal affine stretching forces
quantitative alignment with the top eigendirection. -/
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
  exact (le_div_iff₀ hgamma).2 (by simpa [mul_comm] using hbudget)

/-- The positive-gap hypothesis is genuinely load-bearing: with a repeated top
eigenvalue, a vector orthogonal to the first coordinate can attain the top
Rayleigh quotient exactly. -/
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

end

end NSYuAffineRecurrenceOrientation
