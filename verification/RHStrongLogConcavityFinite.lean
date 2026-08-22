import Mathlib

/-!
# Finite algebra for the strong-log-concavity RH obstruction

Honesty boundary: these theorems verify only polynomial identities and scalar
inequalities used in the Gaussian-polynomial and compact-support counterexamples.
They do not formalize Fourier transforms, complex zero location, Laguerre's
canonical-product theorem, Prékopa's theorem, Pringsheim's theorem, complete
monotonicity, the Riemann Xi function, or RH.
-/

namespace MillenniumBraid.RHStrongLogConcavity

theorem logConcavityPolynomial_decomposition (y : ℝ) :
    y^4 + 4*y^3 + 200*y^2 - 1200*y + 10000 =
      y^4 + 4*y^3 + 100*(y - 6)^2 + 100*y^2 + 6400 := by
  ring

theorem logConcavityPolynomial_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < y^4 + 4*y^3 + 200*y^2 - 1200*y + 10000 := by
  rw [logConcavityPolynomial_decomposition]
  have hy3 : 0 ≤ y^3 := by positivity
  have hy4 : 0 ≤ y^4 := by positivity
  have hsq : 0 ≤ (y - 6)^2 := sq_nonneg (y - 6)
  have hy2 : 0 ≤ y^2 := sq_nonneg y
  nlinarith

theorem fourierPolynomial_pos (y : ℝ) :
    0 < y^2 - 6*y + 103 := by
  nlinarith [sq_nonneg (y - 3)]

theorem fourierDiscriminant :
    (36 : ℝ) - 4 * 103 = -376 := by
  norm_num

theorem dyadicNumerator_identity (s : ℝ) :
    32*s*(s^2 + 12)*(s^4 + 6*s^2 + 103)
      - 8*s*(s^2 + 3)*(s^4 + 24*s^2 + 1648) =
    24*s^3*(s^4 + 15*s^2 - 340) := by
  ring

theorem dyadicNumerator_pos_of_four_le (s : ℝ) (hs : 4 ≤ s) :
    0 < s^4 + 15*s^2 - 340 := by
  have hs2 : 16 ≤ s^2 := by nlinarith [sq_nonneg (s - 4)]
  have hs4 : 256 ≤ s^4 := by nlinarith [sq_nonneg (s^2 - 16)]
  nlinarith

theorem firstQuartic_pos (s : ℝ) : 0 < s^4 + 6*s^2 + 103 := by
  have h2 : 0 ≤ s^2 := sq_nonneg s
  have h4 : 0 ≤ s^4 := by positivity
  nlinarith

theorem secondQuartic_pos (s : ℝ) : 0 < s^4 + 24*s^2 + 1648 := by
  have h2 : 0 ≤ s^2 := sq_nonneg s
  have h4 : 0 ≤ s^4 := by positivity
  nlinarith

theorem laguerreCleared_identity (ε a : ℝ) :
    144*ε^2 - 4*ε*a^2 - 4*ε^2*(36 - a^2) =
      4*ε*(ε - 1)*a^2 := by
  ring

theorem laguerreCleared_neg (ε a : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (ha : 0 < a) :
    4*ε*(ε - 1)*a^2 < 0 := by
  have hεm : ε - 1 < 0 := sub_neg.mpr hε1
  have h4ε : 0 < 4*ε := by positivity
  have hbase : 4*ε*(ε - 1) < 0 :=
    mul_neg_of_pos_of_neg h4ε hεm
  have ha2 : 0 < a^2 := by positivity
  exact mul_neg_of_neg_of_pos hbase ha2

theorem laguerreHalf_exact (a : ℝ) :
    4*(1/2 : ℝ)*((1/2 : ℝ) - 1)*a^2 = -a^2 := by
  ring

theorem convolutionCurvature :
    ((1 : ℝ) * 2) / (1 + 2) = 2 / 3 := by
  norm_num

#print axioms logConcavityPolynomial_decomposition
#print axioms logConcavityPolynomial_pos
#print axioms fourierPolynomial_pos
#print axioms fourierDiscriminant
#print axioms dyadicNumerator_identity
#print axioms dyadicNumerator_pos_of_four_le
#print axioms firstQuartic_pos
#print axioms secondQuartic_pos
#print axioms laguerreCleared_identity
#print axioms laguerreCleared_neg
#print axioms laguerreHalf_exact
#print axioms convolutionCurvature

end MillenniumBraid.RHStrongLogConcavity
