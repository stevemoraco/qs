import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace Millennium.RH.ZetaReflectionPrototype

open Complex

/-- Mathlib's nontrivial-zero conditions, packaged for this prototype. -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
    (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧
    s ≠ 1

lemma nontrivialZero_ne_zero {s : ℂ} (hs : IsNontrivialZero s) : s ≠ 0 := by
  intro h
  subst s
  have hz := hs.1
  rw [riemannZeta_zero] at hz
  norm_num at hz

lemma GammaR_ne_zero_of_nontrivialZero
    {s : ℂ} (hs : IsNontrivialZero s) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
  intro n hn
  cases n with
  | zero =>
      simp only [Nat.cast_zero, mul_zero, neg_zero] at hn
      exact nontrivialZero_ne_zero hs hn
  | succ n =>
      apply hs.2.1
      refine ⟨n, ?_⟩
      simpa [Nat.cast_add, Nat.cast_one] using hn

lemma completedRiemannZeta_eq_zero_of_nontrivialZero
    {s : ℂ} (hs : IsNontrivialZero s) :
    completedRiemannZeta s = 0 := by
  have hs0 : s ≠ 0 := nontrivialZero_ne_zero hs
  have hGamma : Gammaℝ s ≠ 0 := GammaR_ne_zero_of_nontrivialZero hs
  have hz := hs.1
  rw [riemannZeta_def_of_ne_zero hs0] at hz
  exact (div_eq_zero_iff.mp hz).resolve_right hGamma

lemma reflected_riemannZeta_zero
    {s : ℂ} (hs : IsNontrivialZero s) :
    riemannZeta (1 - s) = 0 := by
  have hs1 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs.2.2)
  rw [riemannZeta_def_of_ne_zero hs1, completedRiemannZeta_one_sub,
    completedRiemannZeta_eq_zero_of_nontrivialZero hs, zero_div]

lemma reflected_not_trivial
    {s : ℂ} (hs : IsNontrivialZero s) :
    ¬ ∃ n : ℕ, 1 - s = -2 * (n + 1) := by
  rintro ⟨n, hn⟩
  have hsform : s = 1 + 2 * (n + 1) := by
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 - (-2 * (n + 1)) := by rw [hn]
      _ = 1 + 2 * (n + 1) := by ring
  have hre : 1 ≤ s.re := by
    rw [hsform]
    norm_num
  exact (riemannZeta_ne_zero_of_one_le_re hre) hs.1

lemma reflected_ne_one
    {s : ℂ} (hs : IsNontrivialZero s) :
    1 - s ≠ 1 := by
  intro h
  apply nontrivialZero_ne_zero hs
  calc
    s = 1 - (1 - s) := by ring
    _ = 1 - 1 := by rw [h]
    _ = 0 := by ring

/-- The functional equation reflects every packaged nontrivial zero. -/
theorem reflectsNontrivialZeros :
    ∀ s : ℂ, IsNontrivialZero s → IsNontrivialZero (1 - s) := by
  intro s hs
  exact ⟨reflected_riemannZeta_zero hs, reflected_not_trivial hs,
    reflected_ne_one hs⟩

#print axioms nontrivialZero_ne_zero
#print axioms GammaR_ne_zero_of_nontrivialZero
#print axioms completedRiemannZeta_eq_zero_of_nontrivialZero
#print axioms reflected_riemannZeta_zero
#print axioms reflected_not_trivial
#print axioms reflected_ne_one
#print axioms reflectsNontrivialZeros

end Millennium.RH.ZetaReflectionPrototype
