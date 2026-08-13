import Mathlib

namespace YMFiniteProbeCover

def movingProbe (regulator probe : ℕ) : ℝ :=
  if regulator = probe then 1 else 0

theorem movingProbe_has_local_probe (regulator : ℕ) :
    ∃ probe : ℕ, movingProbe regulator probe = 1 := by
  refine ⟨regulator, ?_⟩
  simp [movingProbe]

theorem movingProbe_each_fixed_eventually_zero (probe : ℕ) :
    ∃ N : ℕ, ∀ regulator : ℕ, N ≤ regulator →
      movingProbe regulator probe = 0 := by
  refine ⟨probe + 1, ?_⟩
  intro regulator hreg
  have hlt : probe < regulator := lt_of_lt_of_le (Nat.lt_succ_self probe) hreg
  have hne : regulator ≠ probe := Nat.ne_of_gt hlt
  simp [movingProbe, hne]

theorem finite_local_probe_sum_lower_bound
    {α : Type*} {m : ℕ}
    (corr : α → Fin m → ℝ) (v : ℝ)
    (hnonneg : ∀ x i, 0 ≤ corr x i)
    (hcover : ∀ x, ∃ i, v ≤ corr x i) :
    ∀ x, v ≤ ∑ i, corr x i := by
  intro x
  rcases hcover x with ⟨i, hi⟩
  have hsingle : corr x i ≤ ∑ j, corr x j := by
    exact Finset.single_le_sum
      (fun j _ => hnonneg x j) (Finset.mem_univ i)
  exact hi.trans hsingle

theorem validated_region_has_local_probe
    {α : Type*} {n m : ℕ}
    (region : Fin n → Set α)
    (probe : Fin n → Fin m)
    (approx error : Fin n → ℝ)
    (corr : α → Fin m → ℝ) (v : ℝ)
    (hcover : ∀ x, ∃ i, x ∈ region i)
    (henclose : ∀ x i, x ∈ region i →
      approx i - error i ≤ corr x (probe i))
    (hmargin : ∀ i, v + error i ≤ approx i) :
    ∀ x, ∃ j, v ≤ corr x j := by
  intro x
  rcases hcover x with ⟨i, hxi⟩
  refine ⟨probe i, ?_⟩
  have hv : v ≤ approx i - error i := by
    linarith [hmargin i]
  exact hv.trans (henclose x i hxi)

theorem validated_region_probe_sum_lower_bound
    {α : Type*} {n m : ℕ}
    (region : Fin n → Set α)
    (probe : Fin n → Fin m)
    (approx error : Fin n → ℝ)
    (corr : α → Fin m → ℝ) (v : ℝ)
    (hcover : ∀ x, ∃ i, x ∈ region i)
    (hnonneg : ∀ x j, 0 ≤ corr x j)
    (henclose : ∀ x i, x ∈ region i →
      approx i - error i ≤ corr x (probe i))
    (hmargin : ∀ i, v + error i ≤ approx i) :
    ∀ x, v ≤ ∑ j, corr x j := by
  apply finite_local_probe_sum_lower_bound corr v hnonneg
  exact validated_region_has_local_probe
    region probe approx error corr v hcover henclose hmargin

theorem positive_sum_has_positive_component
    {m : ℕ} (corr : Fin m → ℝ)
    (hsum : 0 < ∑ i, corr i) :
    ∃ i, 0 < corr i := by
  by_contra hnone
  push_neg at hnone
  have hnonpos : (∑ i, corr i) ≤ 0 := by
    exact Finset.sum_nonpos (fun i _ => hnone i)
  exact (not_lt_of_ge hnonpos) hsum

theorem finite_sum_margin_gives_continuum_probe
    {m : ℕ} (limitCorr : Fin m → ℝ) (v : ℝ)
    (hv : 0 < v)
    (hsum : v ≤ ∑ i, limitCorr i) :
    ∃ i, 0 < limitCorr i := by
  apply positive_sum_has_positive_component limitCorr
  exact lt_of_lt_of_le hv hsum

#print axioms movingProbe_has_local_probe
#print axioms movingProbe_each_fixed_eventually_zero
#print axioms finite_local_probe_sum_lower_bound
#print axioms validated_region_has_local_probe
#print axioms validated_region_probe_sum_lower_bound
#print axioms positive_sum_has_positive_component
#print axioms finite_sum_margin_gives_continuum_probe

end YMFiniteProbeCover
