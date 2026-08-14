import Mathlib

namespace BSDOneLayerExactification

open Finset

/-- Even-level universal Mazur--Tate contribution, written without division. -/
def qEven (p : ℤ) (r : ℕ) : ℤ :=
  ∑ j in range r, (p - 1) * p ^ (2 * j)

/-- Odd-level universal Mazur--Tate contribution, written without division. -/
def qOdd (p : ℤ) (r : ℕ) : ℤ :=
  ∑ j in range r, (p - 1) * p ^ (2 * j + 1)

/-- Closed form `(p+1) q_(2r) = p^(2r)-1`. -/
theorem qEven_closed (p : ℤ) (r : ℕ) :
    (p + 1) * qEven p r = p ^ (2 * r) - 1 := by
  induction r with
  | zero => simp [qEven]
  | succ r ih =>
      rw [qEven, sum_range_succ, qEven] at ih ⊢
      rw [ih]
      ring

/-- Closed form `(p+1) q_(2r+1) = p^(2r+1)-p`. -/
theorem qOdd_closed (p : ℤ) (r : ℕ) :
    (p + 1) * qOdd p r = p ^ (2 * r + 1) - p := by
  induction r with
  | zero => simp [qOdd]
  | succ r ih =>
      rw [qOdd, sum_range_succ, qOdd] at ih ⊢
      rw [ih]
      ring

/-- Complementary even degree `(p+1)(p^(2r)-q)=p^(2r+1)+1`. -/
theorem qEven_complement_closed (p : ℤ) (r : ℕ) :
    (p + 1) * (p ^ (2 * r) - qEven p r) = p ^ (2 * r + 1) + 1 := by
  rw [mul_sub, qEven_closed]
  ring

/-- Complementary odd degree `(p+1)(p^(2r+1)-q)=p^(2r+2)+p`. -/
theorem qOdd_complement_closed (p : ℤ) (r : ℕ) :
    (p + 1) * (p ^ (2 * r + 1) - qOdd p r) = p ^ (2 * r + 2) + p := by
  rw [mul_sub, qOdd_closed]
  ring

/-- Equality of a finite and limiting coefficient prefix transfers the first
nonzero coefficient exactly. -/
theorem first_nonzero_transfers_across_prefix
    {R : Type*} [Zero R]
    (finite limit : ℕ → R) {cutoff index : ℕ}
    (hprefix : ∀ i, i < cutoff → finite i = limit i)
    (hindex : index < cutoff)
    (hzero : ∀ i, i < index → finite i = 0)
    (hnonzero : finite index ≠ 0) :
    (∀ i, i < index → limit i = 0) ∧ limit index ≠ 0 := by
  constructor
  · intro i hi
    rw [← hprefix i (lt_trans hi hindex)]
    exact hzero i hi
  · intro hlim
    apply hnonzero
    calc
      finite index = limit index := hprefix index hindex
      _ = 0 := hlim

/-- The exact finite factorization shifts the finite lambda invariant by `q`. -/
theorem lambda_shift_of_exact_factor
    {q finiteLambda thetaLambda : ℕ}
    (hfactor : thetaLambda = q + finiteLambda) :
    finiteLambda = thetaLambda - q := by
  omega

/-- Combining the factorization and prefix transfer gives the one-layer
signed-lambda exactification identity. -/
theorem one_layer_lambda_exactification
    {q finiteLambda signedLambda thetaLambda : ℕ}
    (hfactor : thetaLambda = q + finiteLambda)
    (htransfer : signedLambda = finiteLambda) :
    signedLambda = thetaLambda - q := by
  omega

/-- The minimal finite residual forces the signed lambda invariant to vanish. -/
theorem minimal_residual_forces_signed_lambda_zero
    {q signedLambda thetaLambda : ℕ}
    (hfactor : thetaLambda = q + signedLambda)
    (hminimal : thetaLambda = q) :
    signedLambda = 0 := by
  omega

/-- Abstract theorem-chain firewall for the rank-zero certificate. The
arithmetic implications remain explicit hypotheses rather than hidden axioms. -/
theorem finite_certificate_implies_rank_zero_pBSD
    {FiniteCertificate SignedUnit ComplexNonzero RankZero PBSD : Prop}
    (hunit : FiniteCertificate → SignedUnit)
    (hnonzero : SignedUnit → ComplexNonzero)
    (hrank : ComplexNonzero → RankZero)
    (hbsd : ComplexNonzero → PBSD)
    (hcert : FiniteCertificate) :
    SignedUnit ∧ ComplexNonzero ∧ RankZero ∧ PBSD := by
  have hu := hunit hcert
  have hn := hnonzero hu
  exact ⟨hu, hn, hrank hn, hbsd hn⟩

/-- A finite prefix cannot identify an infinite series without a proved
congruence cutoff: the two sequences agree below `N` and differ at `N`. -/
def zeroPrefix (_N n : ℕ) : ℕ := 0

def hiddenAtCutoff (N n : ℕ) : ℕ := if n = N then 1 else 0

theorem finite_prefix_agreement_without_global_equality (N : ℕ) :
    (∀ n, n < N → zeroPrefix N n = hiddenAtCutoff N n) ∧
    zeroPrefix N N ≠ hiddenAtCutoff N N := by
  constructor
  · intro n hn
    simp [zeroPrefix, hiddenAtCutoff, Nat.ne_of_lt hn]
  · simp [zeroPrefix, hiddenAtCutoff]

/-- A tiny two-by-two matrix model for the exact `a_p=0` logarithm factors. -/
structure Mat2 (R : Type*) where
  a11 : R
  a12 : R
  a21 : R
  a22 : R

namespace Mat2

variable {R : Type*} [CommRing R]

def mul (A B : Mat2 R) : Mat2 R where
  a11 := A.a11 * B.a11 + A.a12 * B.a21
  a12 := A.a11 * B.a12 + A.a12 * B.a22
  a21 := A.a21 * B.a11 + A.a22 * B.a21
  a22 := A.a21 * B.a12 + A.a22 * B.a22


def cyclotomicStep (eps phi : R) : Mat2 R where
  a11 := 0
  a12 := 1
  a21 := -eps * phi
  a22 := 0


def diagonal (x y : R) : Mat2 R where
  a11 := x
  a12 := 0
  a21 := 0
  a22 := y

/-- Pairing adjacent `a_p=0` logarithm steps gives an exact diagonal block. -/
theorem paired_steps (eps phiOdd phiEven : R) :
    mul (cyclotomicStep eps phiEven) (cyclotomicStep eps phiOdd) =
      diagonal (-eps * phiOdd) (-eps * phiEven) := by
  ext <;> simp [mul, cyclotomicStep, diagonal] <;> ring

end Mat2

#print axioms qEven_closed
#print axioms qOdd_closed
#print axioms qEven_complement_closed
#print axioms qOdd_complement_closed
#print axioms first_nonzero_transfers_across_prefix
#print axioms one_layer_lambda_exactification
#print axioms minimal_residual_forces_signed_lambda_zero
#print axioms finite_certificate_implies_rank_zero_pBSD
#print axioms finite_prefix_agreement_without_global_equality
#print axioms Mat2.paired_steps

end BSDOneLayerExactification
