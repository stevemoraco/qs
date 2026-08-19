import Mathlib

namespace Millennium.YangMills.FaizalShabirTriangularMatchingContraction

def geomEnvelope (q : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => q * geomEnvelope q n + 1

theorem homogeneous_contraction_iterate
    (q D : ℝ)
    (d : ℕ → ℝ)
    (hq : 0 ≤ q)
    (h0 : d 0 ≤ D)
    (hstep : ∀ n, d (n + 1) ≤ q * d n) :
    ∀ n, d n ≤ q ^ n * D := by
  intro n
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      calc
        d (n + 1) ≤ q * d n := hstep n
        _ ≤ q * (q ^ n * D) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (n + 1) * D := by
          rw [pow_succ]
          ring

theorem homogeneous_contraction_hits_budget
    (q D delta : ℝ)
    (d : ℕ → ℝ)
    (m : ℕ)
    (hq : 0 ≤ q)
    (h0 : d 0 ≤ D)
    (hstep : ∀ n, d (n + 1) ≤ q * d n)
    (hbudget : q ^ m * D ≤ delta) :
    d m ≤ delta := by
  exact (homogeneous_contraction_iterate q D d hq h0 hstep m).trans hbudget

theorem affine_contraction_iterate
    (q D eps : ℝ)
    (d : ℕ → ℝ)
    (hq : 0 ≤ q)
    (h0 : d 0 ≤ D)
    (hstep : ∀ n, d (n + 1) ≤ q * d n + eps) :
    ∀ n, d n ≤ q ^ n * D + eps * geomEnvelope q n := by
  intro n
  induction n with
  | zero =>
      simpa [geomEnvelope] using h0
  | succ n ih =>
      calc
        d (n + 1) ≤ q * d n + eps := hstep n
        _ ≤ q * (q ^ n * D + eps * geomEnvelope q n) + eps := by
          have hmul := mul_le_mul_of_nonneg_left ih hq
          nlinarith
        _ = q ^ (n + 1) * D + eps * geomEnvelope q (n + 1) := by
          rw [geomEnvelope, pow_succ]
          ring

theorem affine_contraction_hits_budget
    (q D eps G delta : ℝ)
    (d : ℕ → ℝ)
    (m : ℕ)
    (hq : 0 ≤ q)
    (heps : 0 ≤ eps)
    (h0 : d 0 ≤ D)
    (hstep : ∀ n, d (n + 1) ≤ q * d n + eps)
    (hgeom : geomEnvelope q m ≤ G)
    (hbudget : q ^ m * D + eps * G ≤ delta) :
    d m ≤ delta := by
  have hiter := affine_contraction_iterate q D eps d hq h0 hstep m
  have hforce : eps * geomEnvelope q m ≤ eps * G :=
    mul_le_mul_of_nonneg_left hgeom heps
  have hmid : q ^ m * D + eps * geomEnvelope q m ≤ q ^ m * D + eps * G := by
    nlinarith
  exact hiter.trans (hmid.trans hbudget)

#print axioms homogeneous_contraction_iterate
#print axioms homogeneous_contraction_hits_budget
#print axioms affine_contraction_iterate
#print axioms affine_contraction_hits_budget

end Millennium.YangMills.FaizalShabirTriangularMatchingContraction
