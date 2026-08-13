import Mathlib

namespace SixLaneAudit

theorem hodge_isometric_loop_eq_one_or_neg_one
    {K : Type*} [Field K] (u : K) (hu : u ^ 2 = 1) :
    u = 1 ∨ u = -1 := by
  have hfac : (u - 1) * (u + 1) = 0 := by
    calc
      (u - 1) * (u + 1) = u ^ 2 - 1 := by ring
      _ = 0 := by rw [hu]; ring
  rcases mul_eq_zero.mp hfac with hminus | hplus
  · exact Or.inl (sub_eq_zero.mp hminus)
  · exact Or.inr ((add_eq_zero_iff_eq_neg).mp hplus)

theorem hodge_rational_span_of_isometric_loops
    {K : Type*} [Field K] [Algebra ℚ K]
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (c : ι → ℚ) (u : ι → K)
    (hu : ∀ i ∈ I, u i ^ 2 = 1) :
    ∃ q : ℚ,
      Finset.sum I (fun i => algebraMap ℚ K (c i) * u i) = algebraMap ℚ K q := by
  classical
  refine ⟨Finset.sum I (fun i => if u i = 1 then c i else -c i), ?_⟩
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hpos : u i = 1
  · simp [hpos]
  · have hneg : u i = -1 :=
      (hodge_isometric_loop_eq_one_or_neg_one (u i) (hu i hi)).resolve_left hpos
    simp [hpos, hneg]

theorem hodge_irrational_generator_not_in_rational_span
    {K : Type*} [Field K] [Algebra ℚ K]
    (s : K) (hs : ∀ q : ℚ, s ≠ algebraMap ℚ K q)
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (c : ι → ℚ) (u : ι → K)
    (hu : ∀ i ∈ I, u i ^ 2 = 1) :
    Finset.sum I (fun i => algebraMap ℚ K (c i) * u i) ≠ s := by
  intro hsum
  obtain ⟨q, hq⟩ := hodge_rational_span_of_isometric_loops I c u hu
  exact hs q (hsum.symm.trans hq)

theorem hodge_index_sandwich_base_one
    (j m : ℕ) (hlower : 13 ^ j ∣ m) (hupper : m ∣ 13 * 13 ^ j) :
    m = 13 ^ j ∨ m = 13 ^ (j + 1) := by
  rcases hlower with ⟨k, rfl⟩
  have hpow : 0 < 13 ^ j := pow_pos (by norm_num) j
  have hk : k ∣ 13 := by
    apply Nat.dvd_of_mul_dvd_mul_left hpow
    simpa [Nat.mul_comm] using hupper
  have hp : Nat.Prime 13 := by norm_num
  rcases hp.eq_one_or_self_of_dvd k hk with hk | hk
  · left
    simp [hk]
  · right
    simpa [hk, pow_succ]

theorem hodge_index_sandwich_base_thirteen
    (j m : ℕ) (hlower : 13 ^ j ∣ 13 * m)
    (hupper : 13 * m ∣ 13 * 13 ^ j) :
    m = 13 ^ j ∨ ∃ k : ℕ, j = k + 1 ∧ m = 13 ^ k := by
  have h13 : 0 < (13 : ℕ) := by norm_num
  cases j with
  | zero =>
      left
      have hm : m ∣ 1 := by
        exact Nat.dvd_of_mul_dvd_mul_left h13 (by simpa using hupper)
      simpa using Nat.eq_one_of_dvd_one hm
  | succ j =>
      have hlower' : 13 ^ j ∣ m := by
        apply Nat.dvd_of_mul_dvd_mul_left h13
        simpa [pow_succ, Nat.mul_comm] using hlower
      have hupperRaw : m ∣ 13 ^ (j + 1) := by
        exact Nat.dvd_of_mul_dvd_mul_left h13 hupper
      have hupper' : m ∣ 13 * 13 ^ j := by
        simpa [pow_succ, Nat.mul_comm] using hupperRaw
      rcases hodge_index_sandwich_base_one j m hlower' hupper' with hm | hm
      · right
        exact ⟨j, rfl, hm⟩
      · left
        simpa using hm

end SixLaneAudit
