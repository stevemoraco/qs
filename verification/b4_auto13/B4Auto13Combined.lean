import Mathlib

namespace B4Auto13.RH

theorem sampled_margin_transfer
    {f : ℝ → ℝ} {x a δ L h : ℝ}
    (hδ : 0 < δ)
    (hL : 0 ≤ L)
    (hh : 0 ≤ h)
    (hclose : |x - a| ≤ h)
    (hsample : δ ≤ f a)
    (hlip : f a - L * |x - a| ≤ f x)
    (hmargin : L * h < δ) :
    0 < f x := by
  have hmul : L * |x - a| ≤ L * h :=
    mul_le_mul_of_nonneg_left hclose hL
  nlinarith

#print axioms sampled_margin_transfer
end B4Auto13.RH

namespace B4Auto13.PNP

theorem witness_budget_lower_bound
    {C B k : ℝ}
    (hB : 0 < B)
    (hcover : C ≤ k * B) :
    C / B ≤ k := by
  exact (div_le_iff₀ hB).2 hcover

theorem witness_budget_overload
    {C B k : ℝ}
    (hcover : C ≤ k * B)
    (hover : k * B < C) : False := by
  linarith

#print axioms witness_budget_lower_bound
#print axioms witness_budget_overload
end B4Auto13.PNP

namespace B4Auto13.BSD

theorem defect_budget
    {s r sha d : ℕ}
    (hdecomp : s = r + sha)
    (hnear : s ≤ r + d) :
    sha ≤ d := by
  omega

theorem defect_zero_of_exact_sandwich
    {s r sha : ℕ}
    (hdecomp : s = r + sha)
    (hnear : s ≤ r) :
    sha = 0 := by
  omega

#print axioms defect_budget
#print axioms defect_zero_of_exact_sandwich
end B4Auto13.BSD

namespace B4Auto13.Hodge

theorem index_one_of_discriminant_margin
    {i d D : ℤ}
    (hi : 1 ≤ i)
    (hd : 0 < d)
    (hdisc : D = i * i * d)
    (hnear : D < 4 * d) :
    i = 1 := by
  by_contra hne
  have hi2 : 2 ≤ i := by omega
  have hsq : 4 ≤ i * i := by nlinarith
  have hd0 : 0 ≤ d := by omega
  have hmul : 4 * d ≤ (i * i) * d :=
    mul_le_mul_of_nonneg_right hsq hd0
  nlinarith

#print axioms index_one_of_discriminant_margin
end B4Auto13.Hodge

namespace B4Auto13.NS

theorem episode_packing_bound
    {N E M τ : ℝ}
    (hM : 0 < M)
    (hτ : 0 < τ)
    (hcost : N * (M * M * τ) ≤ E) :
    N ≤ E / (M * M * τ) := by
  have hden : 0 < M * M * τ := by positivity
  exact (le_div_iff₀ hden).2 hcost

#print axioms episode_packing_bound
end B4Auto13.NS

namespace B4Auto13.YM

theorem physical_gap_from_error_budget
    {scaled μ m ε : ℝ}
    (happrox : |scaled - μ| ≤ ε)
    (hcert : m + ε ≤ scaled) :
    m ≤ μ := by
  have hupper : scaled - μ ≤ ε := (abs_le.mp happrox).2
  linarith

theorem physical_gap_strict_from_error_budget
    {scaled μ m ε : ℝ}
    (happrox : |scaled - μ| ≤ ε)
    (hcert : m + ε < scaled) :
    m < μ := by
  have hupper : scaled - μ ≤ ε := (abs_le.mp happrox).2
  linarith

#print axioms physical_gap_from_error_budget
#print axioms physical_gap_strict_from_error_budget
end B4Auto13.YM
