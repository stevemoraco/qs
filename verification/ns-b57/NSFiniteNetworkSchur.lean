import Mathlib

namespace NSFiniteNetworkSchur

open scoped BigOperators

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- The two mixed energy sums are identical after interchanging finite indices. -/
theorem mixed_sum_commutes
    (I : Finset ι) (J : Finset κ)
    (x : ι → ℝ) (a : ι → κ → ℝ) (z : κ → ℝ) :
    (∑ i ∈ I, x i * (∑ j ∈ J, a i j * z j)) =
      ∑ j ∈ J, z j * (∑ i ∈ I, a i j * x i) := by
  calc
    (∑ i ∈ I, x i * (∑ j ∈ J, a i j * z j)) =
        ∑ i ∈ I, ∑ j ∈ J, x i * (a i j * z j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ = ∑ j ∈ J, ∑ i ∈ I, x i * (a i j * z j) := by
          rw [Finset.sum_comm]
    _ = ∑ j ∈ J, z j * (∑ i ∈ I, a i j * x i) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring

/-- Exact energy identity for an arbitrary finite energy-skew carrier/sideband
network with diagonal sideband damping. -/
theorem network_energy_identity
    (I : Finset ι) (J : Finset κ)
    (x : ι → ℝ) (z gamma : κ → ℝ) (a : ι → κ → ℝ) :
    (∑ i ∈ I, x i * (-(∑ j ∈ J, a i j * z j))) +
      (∑ j ∈ J, z j * ((∑ i ∈ I, a i j * x i) - gamma j * z j)) =
    -(∑ j ∈ J, gamma j * (z j) ^ 2) := by
  have hmix := mixed_sum_commutes I J x a z
  have hleft :
      (∑ i ∈ I, x i * (-(∑ j ∈ J, a i j * z j))) =
        -(∑ i ∈ I, x i * (∑ j ∈ J, a i j * z j)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hright :
      (∑ j ∈ J, z j * ((∑ i ∈ I, a i j * x i) - gamma j * z j)) =
        (∑ j ∈ J, z j * (∑ i ∈ I, a i j * x i)) -
          ∑ j ∈ J, gamma j * (z j) ^ 2 := by
    calc
      (∑ j ∈ J, z j * ((∑ i ∈ I, a i j * x i) - gamma j * z j)) =
          ∑ j ∈ J,
            (z j * (∑ i ∈ I, a i j * x i) - gamma j * (z j) ^ 2) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = (∑ j ∈ J, z j * (∑ i ∈ I, a i j * x i)) -
            ∑ j ∈ J, gamma j * (z j) ^ 2 := by
              rw [Finset.sum_sub_distrib]
  rw [hleft, hright, hmix]
  ring

/-- Nonnegative damping makes the network energy pairing nonpositive. -/
theorem network_energy_nonpositive
    (I : Finset ι) (J : Finset κ)
    (x : ι → ℝ) (z gamma : κ → ℝ) (a : ι → κ → ℝ)
    (hgamma : ∀ j ∈ J, 0 ≤ gamma j) :
    (∑ i ∈ I, x i * (-(∑ j ∈ J, a i j * z j))) +
      (∑ j ∈ J, z j * ((∑ i ∈ I, a i j * x i) - gamma j * z j)) ≤ 0 := by
  rw [network_energy_identity]
  exact neg_nonpos.mpr <| Finset.sum_nonneg fun j hj =>
    mul_nonneg (hgamma j hj) (sq_nonneg (z j))

/-- Frozen elimination with arbitrary nonnegative channel weights produces the
negative square-sum Schur energy exactly. -/
theorem weighted_schur_energy_identity
    (I : Finset ι) (J : Finset κ)
    (x : ι → ℝ) (w : κ → ℝ) (a : ι → κ → ℝ) :
    (∑ i ∈ I, x i *
      (-(∑ j ∈ J, a i j * w j * (∑ k ∈ I, a k j * x k)))) =
    -(∑ j ∈ J, w j * (∑ i ∈ I, a i j * x i) ^ 2) := by
  let S : κ → ℝ := fun j => ∑ k ∈ I, a k j * x k
  have hmix := mixed_sum_commutes I J x a (fun j => w j * S j)
  have hleft :
      (∑ i ∈ I, x i *
        (-(∑ j ∈ J, a i j * w j * S j))) =
      -(∑ i ∈ I, x i * (∑ j ∈ J, a i j * (w j * S j))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [show (∑ i ∈ I, x i *
      (-(∑ j ∈ J, a i j * w j * (∑ k ∈ I, a k j * x k)))) =
      (∑ i ∈ I, x i * (-(∑ j ∈ J, a i j * w j * S j))) by rfl]
  rw [hleft, hmix]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  change (w j * S j) * S j = w j * S j ^ 2
  ring

/-- The frozen Schur carrier energy is nonpositive for nonnegative channel
weights, in particular for reciprocal positive damping rates. -/
theorem weighted_schur_nonpositive
    (I : Finset ι) (J : Finset κ)
    (x : ι → ℝ) (w : κ → ℝ) (a : ι → κ → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j) :
    (∑ i ∈ I, x i *
      (-(∑ j ∈ J, a i j * w j * (∑ k ∈ I, a k j * x k)))) ≤ 0 := by
  rw [weighted_schur_energy_identity]
  exact neg_nonpos.mpr <| Finset.sum_nonneg fun j hj =>
    mul_nonneg (hw j hj) (sq_nonneg (∑ i ∈ I, a i j * x i))

#print axioms mixed_sum_commutes
#print axioms network_energy_identity
#print axioms network_energy_nonpositive
#print axioms weighted_schur_energy_identity
#print axioms weighted_schur_nonpositive

end NSFiniteNetworkSchur
