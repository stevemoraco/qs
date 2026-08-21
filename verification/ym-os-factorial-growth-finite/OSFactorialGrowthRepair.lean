import Mathlib

namespace Millennium.YangMills

def HasFactorialPowerGrowthAt (c : ℕ → ℝ) (B : ℕ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, |c n| ≤ A * (Nat.factorial n : ℝ) ^ B

theorem factorialPowerGrowth_zero (B : ℕ) :
    HasFactorialPowerGrowthAt (fun _ : ℕ => (0 : ℝ)) B := by
  refine ⟨0, le_rfl, ?_⟩
  intro n
  simp

theorem factorialPowerGrowth_add
    {a b : ℕ → ℝ} {B : ℕ}
    (ha : HasFactorialPowerGrowthAt a B)
    (hb : HasFactorialPowerGrowthAt b B) :
    HasFactorialPowerGrowthAt (fun n => a n + b n) B := by
  rcases ha with ⟨A, hA, ha⟩
  rcases hb with ⟨C, hC, hb⟩
  refine ⟨A + C, add_nonneg hA hC, ?_⟩
  intro n
  calc
    |a n + b n| ≤ |a n| + |b n| := abs_add _ _
    _ ≤ A * (Nat.factorial n : ℝ) ^ B +
          C * (Nat.factorial n : ℝ) ^ B := add_le_add (ha n) (hb n)
    _ = (A + C) * (Nat.factorial n : ℝ) ^ B := by ring

theorem factorialPowerGrowth_mul
    {a b : ℕ → ℝ} {B₁ B₂ : ℕ}
    (ha : HasFactorialPowerGrowthAt a B₁)
    (hb : HasFactorialPowerGrowthAt b B₂) :
    HasFactorialPowerGrowthAt (fun n => a n * b n) (B₁ + B₂) := by
  rcases ha with ⟨A, hA, ha⟩
  rcases hb with ⟨C, hC, hb⟩
  refine ⟨A * C, mul_nonneg hA hC, ?_⟩
  intro n
  have hfactor₁ : 0 ≤ (Nat.factorial n : ℝ) ^ B₁ := by positivity
  calc
    |a n * b n| = |a n| * |b n| := abs_mul _ _
    _ ≤ (A * (Nat.factorial n : ℝ) ^ B₁) * |b n| :=
      mul_le_mul_of_nonneg_right (ha n) (abs_nonneg (b n))
    _ ≤ (A * (Nat.factorial n : ℝ) ^ B₁) *
          (C * (Nat.factorial n : ℝ) ^ B₂) :=
      mul_le_mul_of_nonneg_left (hb n) (mul_nonneg hA hfactor₁)
    _ = (A * C) * (Nat.factorial n : ℝ) ^ (B₁ + B₂) := by
      rw [pow_add]
      ring

theorem factorialPowerGrowth_of_exponential_absorption
    (c : ℕ → ℝ) (K A : ℝ) (B Q : ℕ)
    (hA : 0 ≤ A)
    (hc : ∀ n : ℕ,
      |c n| ≤ K ^ n * (Nat.factorial n : ℝ) ^ B)
    (habsorb : ∀ n : ℕ,
      K ^ n ≤ A * (Nat.factorial n : ℝ) ^ Q) :
    HasFactorialPowerGrowthAt c (Q + B) := by
  refine ⟨A, hA, ?_⟩
  intro n
  have hfactor : 0 ≤ (Nat.factorial n : ℝ) ^ B := by positivity
  calc
    |c n| ≤ K ^ n * (Nat.factorial n : ℝ) ^ B := hc n
    _ ≤ (A * (Nat.factorial n : ℝ) ^ Q) *
          (Nat.factorial n : ℝ) ^ B :=
      mul_le_mul_of_nonneg_right (habsorb n) hfactor
    _ = A * (Nat.factorial n : ℝ) ^ (Q + B) := by
      rw [pow_add]
      ring

def hostileFactorialCoefficient (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) ^ 2

theorem hostileFactorialCoefficient_has_factorial_growth :
    HasFactorialPowerGrowthAt hostileFactorialCoefficient 2 := by
  refine ⟨1, by norm_num, ?_⟩
  intro n
  simp [hostileFactorialCoefficient, abs_of_nonneg]

theorem labelledTreeFactorialCost
    {c : ℕ → ℝ} {B : ℕ}
    (hc : HasFactorialPowerGrowthAt c B) :
    HasFactorialPowerGrowthAt
      (fun n => c n * (Nat.factorial n : ℝ)) (B + 1) := by
  have hfactorial :
      HasFactorialPowerGrowthAt
        (fun n : ℕ => (Nat.factorial n : ℝ)) 1 := by
    refine ⟨1, by norm_num, ?_⟩
    intro n
    simp [abs_of_nonneg]
  simpa using factorialPowerGrowth_mul hc hfactorial

#print axioms factorialPowerGrowth_zero
#print axioms factorialPowerGrowth_add
#print axioms factorialPowerGrowth_mul
#print axioms factorialPowerGrowth_of_exponential_absorption
#print axioms hostileFactorialCoefficient_has_factorial_growth
#print axioms labelledTreeFactorialCost

end Millennium.YangMills
