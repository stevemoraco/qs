import Mathlib

/-!
# Polynomial-padding exponent conservation for the CJW sparse-NP route

Finite ordered-field core only. This does not formalize complexity classes.

Interpretation:
* `ε` = source hierarchy hardness/sparsity exponent;
* `δ` = fixed target hardness exponent required by magnification;
* `a` = padding power, `N ≍ n^a`;
* `β` = target sparsity exponent.

The hypotheses encode:
  ε ≤ β a              (padding made the source sparse enough)
  a(1+δ) ≤ 1+ε         (target running time still lies inside source lower bound)
  1 ≤ a.
They force β ≥ δ, so polynomial padding cannot reach arbitrarily small β while
preserving one fixed δ>0.
-/

namespace PvsNPBraid

/-- Time-preserving polynomial padding forces the target hardness exponent not
    to exceed the source exponent. -/
theorem padding_forces_delta_le_epsilon
    (ε δ a : ℝ)
    (hδ : 0 ≤ δ)
    (ha : 1 ≤ a)
    (htime : a * (1 + δ) ≤ 1 + ε) :
    δ ≤ ε := by
  have hpos : 0 ≤ 1 + δ := by linarith
  have hmul : 1 + δ ≤ a * (1 + δ) := by
    nlinarith
  linarith

/-- Exact cross-exponent conservation inequality. -/
theorem padding_cross_exponent
    (ε δ a β : ℝ)
    (hε : 0 ≤ ε)
    (hδ : 0 ≤ δ)
    (hβ : 0 ≤ β)
    (hsparse : ε ≤ β * a)
    (htime : a * (1 + δ) ≤ 1 + ε) :
    ε * (1 + δ) ≤ β * (1 + ε) := by
  have h1δ : 0 ≤ 1 + δ := by linarith
  have hstep1 : ε * (1 + δ) ≤ (β * a) * (1 + δ) :=
    mul_le_mul_of_nonneg_right hsparse h1δ
  have hstep2 : β * (a * (1 + δ)) ≤ β * (1 + ε) :=
    mul_le_mul_of_nonneg_left htime hβ
  calc
    ε * (1 + δ) ≤ (β * a) * (1 + δ) := hstep1
    _ = β * (a * (1 + δ)) := by ring
    _ ≤ β * (1 + ε) := hstep2

/-- Combining sparsity and time preservation with genuine padding (`a ≥ 1`)
    gives the sharp simple obstruction `δ ≤ β`. -/
theorem polynomial_padding_cannot_reduce_below_target_hardness
    (ε δ a β : ℝ)
    (hε : 0 ≤ ε)
    (hδ : 0 ≤ δ)
    (hβ : 0 ≤ β)
    (ha : 1 ≤ a)
    (hsparse : ε ≤ β * a)
    (htime : a * (1 + δ) ≤ 1 + ε) :
    δ ≤ β := by
  have hδε : δ ≤ ε := padding_forces_delta_le_epsilon ε δ a hδ ha htime
  have hcross := padding_cross_exponent ε δ a β hε hδ hβ hsparse htime
  have h1ε : 0 < 1 + ε := by linarith
  nlinarith

end PvsNPBraid
