import Mathlib

namespace RH
namespace C486PositiveCompanionFinite

theorem coefficient_cone_sufficient
    {a minusB convolution primeRow : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ minusB)
    (hc : 0 ≤ convolution) (hp : 0 ≤ primeRow) :
    0 ≤ a * convolution + minusB * primeRow := by positivity

theorem positive_b_fails_prime_row {b primeRow : ℝ}
    (hb : 0 < b) (hp : 0 < primeRow) :
    -b * primeRow < 0 := by nlinarith

theorem negative_a_fails_semiprime_row {a convolution : ℝ}
    (ha : a < 0) (hc : 0 < convolution) :
    a * convolution < 0 := by
  exact mul_neg_of_neg_of_pos ha hc

def zeroDoubleCoefficient (m lambda : ℝ) : ℝ :=
  m * (m - lambda)

theorem zeroDoubleCoefficient_identity (m lambda : ℝ) :
    zeroDoubleCoefficient m lambda = m ^ 2 - lambda * m := by ring

theorem zeroDoubleCoefficient_nonneg
    {m lambda : ℝ}
    (hm : 1 ≤ m) (_hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) :
    0 ≤ zeroDoubleCoefficient m lambda := by
  unfold zeroDoubleCoefficient
  have hm0 : 0 ≤ m := le_trans (by norm_num) hm
  have hdiff : 0 ≤ m - lambda := by linarith
  exact mul_nonneg hm0 hdiff

theorem simpleZero_nonblind
    {lambda : ℝ} (_hl0 : 0 ≤ lambda) (hl1 : lambda < 1) :
    0 < zeroDoubleCoefficient 1 lambda := by
  unfold zeroDoubleCoefficient
  linarith

theorem simpleZero_endpoint_blind :
    zeroDoubleCoefficient 1 1 = 0 := by norm_num [zeroDoubleCoefficient]

theorem companion_affine_collapse
    (A2 Aprime lambda : ℝ) :
    (A2 - lambda * Aprime) - (A2 - Aprime) =
      (1 - lambda) * Aprime := by ring

theorem continuousDensity_nonneg
    {r cosine : ℝ}
    (_hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (hcos : cosine ≤ 1) :
    0 ≤ 1 - 2 * r * cosine := by
  have hmul : r * cosine ≤ r := by nlinarith
  nlinarith

theorem prescribedZero_residue (lambda : ℝ) :
    (-1 : ℝ) * ((-1) + lambda) = 1 - lambda := by ring

theorem prescribedPole_residue (lambda : ℝ) :
    (1 : ℝ) * (1 + lambda) = 1 + lambda := by ring

#print axioms coefficient_cone_sufficient
#print axioms zeroDoubleCoefficient_nonneg
#print axioms simpleZero_nonblind
#print axioms companion_affine_collapse
#print axioms continuousDensity_nonneg
#print axioms prescribedZero_residue

end C486PositiveCompanionFinite
end RH
