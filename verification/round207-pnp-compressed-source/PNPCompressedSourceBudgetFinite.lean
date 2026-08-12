import Mathlib

/-!
# Round 207 compressed-source exponent budget

This file formalizes only elementary exponent and scaling identities. It does
not formalize exponential-time hierarchy classes, sparse encodings, circuit
lower bounds, hardness magnification, NP, or P versus NP.
-/

namespace Millennium
namespace Round207PNP

/-- A polynomial in an ambient exponential length is still exponential in the
compressed descriptor length. -/
theorem ambient_polynomial_is_descriptor_exponential
    (base k d : ℕ) :
    (base ^ k) ^ d = base ^ (k * d) := by
  exact pow_mul base k d

/-- A positive exponential-time coefficient remains a positive polynomial
exponent after changing variables `N = exp(gamma*k)`. -/
theorem positive_compressed_runtime_exponent
    (beta gamma : ℝ) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    0 < beta / gamma := by
  exact div_pos hbeta hgamma

/-- Beating an encoder exponent and making the compressed source exponent zero
are incompatible when the source has genuinely positive exponential-time
coefficient. -/
theorem no_zero_runtime_exponent_for_positive_source
    (alpha beta gamma : ℝ)
    (halphaGamma : gamma < alpha)
    (hbeta : 0 < beta)
    (hgamma : 0 < gamma) :
    gamma < alpha ∧ beta / gamma ≠ 0 := by
  refine ⟨halphaGamma, ne_of_gt ?_⟩
  exact positive_compressed_runtime_exponent beta gamma hbeta hgamma

/-- Ordinary componentwise polynomial padding conserves the basic verifier /
hardness exponent budget. -/
theorem padding_ratio_budget
    (verifier hardness padding targetVerifier targetHardness : ℝ)
    (hTargetVerifier : 0 ≤ targetVerifier)
    (hTargetHardness : 0 ≤ targetHardness)
    (hverifier : verifier ≤ padding * targetVerifier)
    (hhardness : padding * targetHardness ≤ hardness) :
    verifier * targetHardness ≤ hardness * targetVerifier := by
  calc
    verifier * targetHardness ≤
        (padding * targetVerifier) * targetHardness :=
      mul_le_mul_of_nonneg_right hverifier hTargetHardness
    _ = (padding * targetHardness) * targetVerifier := by ring
    _ ≤ hardness * targetVerifier :=
      mul_le_mul_of_nonneg_right hhardness hTargetVerifier

/-- A pointwise existence statement is not syntactically the same statement as
one witness satisfying all indices. This theorem records only the forward
implication from a uniform witness. -/
theorem uniform_witness_implies_pointwise
    {N S : Type*} (Good : N → S → Prop)
    (s : S) (huniform : ∀ n, Good n s) :
    ∀ n, ∃ t, Good n t := by
  intro n
  exact ⟨s, huniform n⟩

#print axioms ambient_polynomial_is_descriptor_exponential
#print axioms positive_compressed_runtime_exponent
#print axioms no_zero_runtime_exponent_for_positive_source
#print axioms padding_ratio_budget
#print axioms uniform_witness_implies_pointwise

end Round207PNP
end Millennium
