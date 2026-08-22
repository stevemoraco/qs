import Mathlib

namespace Millennium.YangMills

/-- A small helper used to avoid relying on a specialized power-monotonicity lemma. -/
theorem pow_le_pow_of_nonneg
    (a b : ℝ)
    (ha : 0 ≤ a)
    (hab : a ≤ b) :
    ∀ n : ℕ, a ^ n ≤ b ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hb : 0 ≤ b := le_trans ha hab
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hab ha (pow_nonneg hb n)

/-- Every natural predecessor is dominated by the corresponding power of two. -/
theorem nat_pred_le_two_pow (n : ℕ) :
    n - 1 ≤ 2 ^ n := by
  calc
    n - 1 ≤ n := Nat.sub_le n 1
    _ ≤ 2 * n := by omega
    _ ≤ 2 ^ n := Nat.mul_le_pow (by decide : 2 ≠ 1) n

/-- Real-cast form of `nat_pred_le_two_pow`. -/
theorem nat_pred_cast_le_two_pow (n : ℕ) :
    ((n - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
  exact_mod_cast nat_pred_le_two_pow n

/-- If `a ≥ 1`, deleting one exponent can only decrease `a^n`. -/
theorem pow_pred_le_pow
    (a : ℝ)
    (n : ℕ)
    (ha : 1 ≤ a) :
    a ^ (n - 1) ≤ a ^ n := by
  cases n with
  | zero => simp
  | succ n =>
      have ha0 : 0 ≤ a := le_trans (by norm_num) ha
      rw [Nat.succ_sub_one, pow_succ]
      simpa using mul_le_mul_of_nonneg_left ha (pow_nonneg ha0 n)

/-- If `a ≥ 1` and `n ≥ 2`, deleting two exponents can only decrease `a^n`. -/
theorem pow_sub_two_le_pow
    (a : ℝ)
    (n : ℕ)
    (ha : 1 ≤ a)
    (hn : 2 ≤ n) :
    a ^ (n - 2) ≤ a ^ n := by
  have hn_eq : n = (n - 2) + 2 := by omega
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have ha2 : 1 ≤ a ^ 2 := by
    nlinarith [sq_nonneg (a - 1)]
  rw [hn_eq, pow_add]
  simpa using mul_le_mul_of_nonneg_left ha2 (pow_nonneg ha0 (n - 2))

/--
The value-row branching factor `(1+B)^(n-1)` is absorbed by one explicit
exponential incidence charge with base `2(1+B)`. This is the finite algebra
behind replacing the unit branch ball in Kirk v4 Lemma 6.38 by any fixed
finite branch radius.
-/
theorem value_weight_le_doubled_charge
    (a : ℝ)
    (n : ℕ)
    (ha : 1 ≤ a) :
    a ^ (n - 1) ≤ (2 * a) ^ n := by
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have hpred : a ^ (n - 1) ≤ a ^ n := pow_pred_le_pow a n ha
  have htwo : 1 ≤ (2 : ℝ) ^ n := by positivity
  have hscale : a ^ n ≤ (2 : ℝ) ^ n * a ^ n := by
    simpa using mul_le_mul_of_nonneg_right htwo (pow_nonneg ha0 n)
  calc
    a ^ (n - 1) ≤ a ^ n := hpred
    _ ≤ (2 : ℝ) ^ n * a ^ n := hscale
    _ = (2 * a) ^ n := by rw [mul_pow]

/--
The differentiated branching factor `(n-1) a^(n-2)` is absorbed by the
same explicit charge `(2a)^n` whenever an activity has at least two pivot
incidences.
-/
theorem derivative_weight_le_doubled_charge
    (a : ℝ)
    (n : ℕ)
    (ha : 1 ≤ a)
    (hn : 2 ≤ n) :
    ((n - 1 : ℕ) : ℝ) * a ^ (n - 2) ≤ (2 * a) ^ n := by
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have hcoeff : ((n - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n :=
    nat_pred_cast_le_two_pow n
  have hpow : a ^ (n - 2) ≤ a ^ n := pow_sub_two_le_pow a n ha hn
  have hmul :
      ((n - 1 : ℕ) : ℝ) * a ^ (n - 2) ≤
        (2 : ℝ) ^ n * a ^ n :=
    mul_le_mul hcoeff hpow (pow_nonneg ha0 (n - 2)) (by positivity)
  calc
    ((n - 1 : ℕ) : ℝ) * a ^ (n - 2)
        ≤ (2 : ℝ) ^ n * a ^ n := hmul
    _ = (2 * a) ^ n := by rw [mul_pow]

/-- Finite-family value rows inherit the same charge domination termwise. -/
theorem finite_value_row_dominated
    {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι)
    (a : ℝ)
    (incidence : ι → ℕ)
    (weight : ι → ℝ)
    (ha : 1 ≤ a)
    (hweight : ∀ i ∈ s, 0 ≤ weight i) :
    (∑ i ∈ s, a ^ (incidence i - 1) * weight i) ≤
      ∑ i ∈ s, (2 * a) ^ incidence i * weight i := by
  refine Finset.sum_le_sum ?_
  intro i hi
  exact mul_le_mul_of_nonneg_right
    (value_weight_le_doubled_charge a (incidence i) ha)
    (hweight i hi)

/-- Finite-family differentiated rows inherit the same charge domination. -/
theorem finite_derivative_row_dominated
    {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι)
    (a : ℝ)
    (incidence : ι → ℕ)
    (weight : ι → ℝ)
    (ha : 1 ≤ a)
    (hincidence : ∀ i ∈ s, 2 ≤ incidence i)
    (hweight : ∀ i ∈ s, 0 ≤ weight i) :
    (∑ i ∈ s,
        ((incidence i - 1 : ℕ) : ℝ) *
          a ^ (incidence i - 2) * weight i) ≤
      ∑ i ∈ s, (2 * a) ^ incidence i * weight i := by
  refine Finset.sum_le_sum ?_
  intro i hi
  have hrow := derivative_weight_le_doubled_charge
    a (incidence i) ha (hincidence i hi)
  exact mul_le_mul_of_nonneg_right hrow (hweight i hi)

/-- The scalar rooted branch map appearing in the generalized recursion. -/
def generalizedBranchMap
    (J epsInf epsOne Xi x : ℝ)
    (degree : ℕ) : ℝ :=
  J * (1 + epsInf * (1 + x)) ^ (degree - 1) *
      (1 + epsOne) ^ degree * Real.exp Xi - 1

/--
A single endpoint admission inequality at radius `B` controls the entire
nonlinear rooted recursion on `[0,B]`. The only ingredients are nonnegative
rows and an upper bound on the activity exponent. This closes the finite
nonlinear monotonicity step left implicit in the enlarged-branch-ball note.
-/
theorem generalized_branch_ball_invariant
    (J epsInf epsOne Xi XiMax B x : ℝ)
    (degree : ℕ)
    (hJ : 0 ≤ J)
    (hInf : 0 ≤ epsInf)
    (hOne : 0 ≤ epsOne)
    (hB : 0 ≤ B)
    (hx0 : 0 ≤ x)
    (hxB : x ≤ B)
    (hXi : Xi ≤ XiMax)
    (hadmit : generalizedBranchMap J epsInf epsOne XiMax B degree ≤ B) :
    generalizedBranchMap J epsInf epsOne Xi x degree ≤ B := by
  have hbase0 : 0 ≤ 1 + epsInf * (1 + x) := by nlinarith
  have hbaseB0 : 0 ≤ 1 + epsInf * (1 + B) := by nlinarith
  have hbase :
      1 + epsInf * (1 + x) ≤ 1 + epsInf * (1 + B) := by
    nlinarith
  have hpow :
      (1 + epsInf * (1 + x)) ^ (degree - 1) ≤
        (1 + epsInf * (1 + B)) ^ (degree - 1) :=
    pow_le_pow_of_nonneg
      (1 + epsInf * (1 + x))
      (1 + epsInf * (1 + B))
      hbase0 hbase (degree - 1)
  have honebase : 0 ≤ 1 + epsOne := by linarith
  have honepow : 0 ≤ (1 + epsOne) ^ degree := pow_nonneg honebase degree
  have hleft0 :
      0 ≤ J * (1 + epsInf * (1 + x)) ^ (degree - 1) *
        (1 + epsOne) ^ degree := by positivity
  have hright0 :
      0 ≤ J * (1 + epsInf * (1 + B)) ^ (degree - 1) *
        (1 + epsOne) ^ degree := by positivity
  have hcore :
      J * (1 + epsInf * (1 + x)) ^ (degree - 1) *
          (1 + epsOne) ^ degree ≤
        J * (1 + epsInf * (1 + B)) ^ (degree - 1) *
          (1 + epsOne) ^ degree := by
    have hJpow := mul_le_mul_of_nonneg_left hpow hJ
    exact mul_le_mul_of_nonneg_right hJpow honepow
  have hexp : Real.exp Xi ≤ Real.exp XiMax := Real.exp_le_exp.mpr hXi
  have hproduct :
      J * (1 + epsInf * (1 + x)) ^ (degree - 1) *
          (1 + epsOne) ^ degree * Real.exp Xi ≤
        J * (1 + epsInf * (1 + B)) ^ (degree - 1) *
          (1 + epsOne) ^ degree * Real.exp XiMax :=
    mul_le_mul hcore hexp (Real.exp_pos Xi).le hright0
  unfold generalizedBranchMap at hadmit ⊢
  exact le_trans (sub_le_sub_right hproduct 1) hadmit

#print axioms pow_le_pow_of_nonneg
#print axioms nat_pred_le_two_pow
#print axioms nat_pred_cast_le_two_pow
#print axioms pow_pred_le_pow
#print axioms pow_sub_two_le_pow
#print axioms value_weight_le_doubled_charge
#print axioms derivative_weight_le_doubled_charge
#print axioms finite_value_row_dominated
#print axioms finite_derivative_row_dominated
#print axioms generalized_branch_ball_invariant

end Millennium.YangMills
