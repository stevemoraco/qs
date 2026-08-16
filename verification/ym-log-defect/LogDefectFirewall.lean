import Mathlib

/-!
# Yang--Mills logarithmic defect firewall — public replay mirror

Correct scalar inequality only. No Yang--Mills construction or mass-gap theorem.
-/

namespace Millennium.YangMills

/-- Correct universal additive-eigenvalue to logarithmic-loss inequality. -/
theorem neg_log_add_ge_neg_log_sub_div
    (lambda epsilon : ℝ)
    (hlambda : 0 < lambda)
    (hepsilon : 0 ≤ epsilon) :
    -Real.log (lambda + epsilon) ≥
      -Real.log lambda - epsilon / lambda := by
  have hsum : 0 < lambda + epsilon := by
    linarith
  have hratio : 0 < (lambda + epsilon) / lambda :=
    div_pos hsum hlambda
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div (ne_of_gt hsum) (ne_of_gt hlambda)] at hlog
  have hratio_sub :
      (lambda + epsilon) / lambda - 1 = epsilon / lambda := by
    field_simp [ne_of_gt hlambda]
    ring
  rw [hratio_sub] at hlog
  linarith

/-- A scaled form making the physical `1/a` tax explicit. -/
theorem neg_log_add_div_scale_ge
    (a lambda epsilon : ℝ)
    (ha : 0 < a)
    (hlambda : 0 < lambda)
    (hepsilon : 0 ≤ epsilon) :
    (-Real.log (lambda + epsilon)) / a ≥
      (-Real.log lambda) / a - epsilon / (a * lambda) := by
  have h := neg_log_add_ge_neg_log_sub_div lambda epsilon hlambda hepsilon
  have ha0 : 0 ≤ (1 / a) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left h ha0
  field_simp [ne_of_gt ha, ne_of_gt hlambda] at hscaled ⊢
  nlinarith

#print axioms neg_log_add_ge_neg_log_sub_div
#print axioms neg_log_add_div_scale_ge

end Millennium.YangMills
