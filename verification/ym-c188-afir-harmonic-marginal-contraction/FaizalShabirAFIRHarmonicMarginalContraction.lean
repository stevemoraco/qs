import Mathlib

/-!
# AF/IR harmonic marginal-contraction core

Finite real-algebra core for the C188 repair of the Faizal--Shabir AF/IR
identification gate.  The manuscript's one-loop marginal map has cubic form
`g ↦ g - beta * g^3`.  Differences of two trajectories therefore carry an
exact multiplier `1 - beta*(g^2+g*h+h^2)`.  Along asymptotically-free
trajectories `g^2 ~ const/k`, this is precisely harmonic-scale contraction,
not a summable additive error.

This file formalizes only the exact cubic factorization and a one-step weighted
rescaling identity used by the human discrete contraction argument.  It does
not formalize the Faizal--Shabir remainder bounds, RG orientation, Schwinger
functions, Yang--Mills, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirAFIRHarmonicMarginalContraction

theorem cubic_beta_difference_factorization
    (g h beta : ℝ) :
    (g - beta * g ^ 3) - (h - beta * h ^ 3) =
      (g - h) * (1 - beta * (g ^ 2 + g * h + h ^ 2)) := by
  ring

theorem cubic_beta_abs_difference
    (g h beta : ℝ)
    (hmul : 0 ≤ 1 - beta * (g ^ 2 + g * h + h ^ 2)) :
    |(g - beta * g ^ 3) - (h - beta * h ^ 3)| =
      (1 - beta * (g ^ 2 + g * h + h ^ 2)) * |g - h| := by
  rw [cubic_beta_difference_factorization]
  rw [abs_mul, abs_of_nonneg hmul]
  ring

theorem harmonic_weighted_step
    (n q d dnext eps : ℝ)
    (hn : 0 ≤ n)
    (hq : (n + 1) * q = n)
    (hstep : dnext ≤ q * d + eps) :
    (n + 1) * dnext ≤ n * d + (n + 1) * eps := by
  have hnp1 : 0 ≤ n + 1 := by linarith
  have hmul : (n + 1) * dnext ≤ (n + 1) * (q * d + eps) :=
    mul_le_mul_of_nonneg_left hstep hnp1
  have hqd0 := congrArg (fun z : ℝ => z * d) hq
  have hqd : (n + 1) * (q * d) = n * d := by
    simpa [mul_assoc] using hqd0
  calc
    (n + 1) * dnext ≤ (n + 1) * (q * d + eps) := hmul
    _ = (n + 1) * (q * d) + (n + 1) * eps := by ring
    _ = n * d + (n + 1) * eps := by rw [hqd]

theorem harmonic_factor_lt_one
    (n : ℝ)
    (hn : 0 ≤ n) :
    n / (n + 1) < 1 := by
  have hnp1 : 0 < n + 1 := by linarith
  exact (div_lt_iff₀ hnp1).2 (by linarith)

theorem harmonic_factor_complement
    (n : ℝ)
    (hn : 0 ≤ n) :
    1 - n / (n + 1) = 1 / (n + 1) := by
  have hne : n + 1 ≠ 0 := by linarith
  field_simp
  ring

#print axioms cubic_beta_difference_factorization
#print axioms cubic_beta_abs_difference
#print axioms harmonic_weighted_step
#print axioms harmonic_factor_lt_one
#print axioms harmonic_factor_complement

end Millennium.YangMills.FaizalShabirAFIRHarmonicMarginalContraction
