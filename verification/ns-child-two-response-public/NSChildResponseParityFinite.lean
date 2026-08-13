import Mathlib

namespace NSChildResponseParityFinite

/-!
Finite real-algebra shadow of the response-parity splitter.

The human theorem asks for one packet involution under which the parent response
is even and the child response is odd.  This file formalizes only the resulting
`2 x 2` algebra.  It does not construct an involution, Fourier packet, Leray
response, Navier--Stokes solution, or blow-up.
-/

/-- Determinant of two response columns. -/
def det2 (p1 p2 c1 c2 : ℝ) : ℝ := p1 * c2 - p2 * c1

/-- Opposite response parity produces an explicit determinant. -/
theorem parity_pair_determinant (p c : ℝ) :
    det2 p p c (-c) = -2 * p * c := by
  unfold det2
  ring

/-- Equal weights add the even response and cancel the odd response exactly. -/
theorem equal_weight_neutral_repair
    {r p c : ℝ} (hp : p ≠ 0) :
    p * (r / (2 * p)) + p * (r / (2 * p)) = r ∧
      c * (r / (2 * p)) + (-c) * (r / (2 * p)) = 0 := by
  constructor
  · field_simp [hp]
    <;> ring
  · ring

/-- For a nonnegative target and a positively oriented even response, the exact
neutral repair lies in the nonnegative coefficient cone. -/
theorem equal_weight_positive_cone
    {r p : ℝ} (hr : 0 ≤ r) (hp : 0 < p) :
    0 ≤ r / (2 * p) := by
  exact div_nonneg hr (mul_nonneg (by norm_num) (le_of_lt hp))

/-- Exact determinant perturbation identity around an ideal parity pair. -/
theorem parity_determinant_perturbation_identity
    (p c e1 e2 f1 f2 : ℝ) :
    det2 (p + e1) (p + e2) (c + f1) (-c + f2) -
        (-2 * p * c) =
      p * (f2 - f1) - c * (e1 + e2) + e1 * f2 - e2 * f1 := by
  unfold det2
  ring

/-- Abstract robust lower bound after the explicit parity determinant has been
perturbed by at most the stated error budget. -/
theorem parity_determinant_stability
    {p c pert H a b C eta : ℝ}
    (hbase : 2 * a * b * H ^ 2 ≤ |-2 * p * c|)
    (herr : |pert - (-2 * p * c)| ≤
      (4 * C * eta + 2 * eta ^ 2) * H ^ 2) :
    (2 * a * b - 4 * C * eta - 2 * eta ^ 2) * H ^ 2 ≤
      |pert| := by
  have htri : |-2 * p * c| ≤ |pert| + |-2 * p * c - pert| := by
    calc
      |-2 * p * c| = |pert + (-2 * p * c - pert)| := by ring_nf
      _ ≤ |pert| + |-2 * p * c - pert| := abs_add _ _
  rw [abs_sub_comm] at htri
  nlinarith

#print axioms parity_pair_determinant
#print axioms equal_weight_neutral_repair
#print axioms equal_weight_positive_cone
#print axioms parity_determinant_perturbation_identity
#print axioms parity_determinant_stability

end NSChildResponseParityFinite
