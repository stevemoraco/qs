import Mathlib

namespace YMFiniteOSWitnessCover

theorem trace_tail_lower
    {M : ℕ} (g gK : Fin M → ℝ) (δ : ℝ)
    (herr : ∀ i, |g i - gK i| ≤ δ) :
    (∑ i, gK i) - (M : ℝ) * δ ≤ ∑ i, g i := by
  have hpoint : ∀ i, gK i - δ ≤ g i := by
    intro i
    have h := (abs_le.mp (herr i)).1
    linarith
  have hsum : (∑ i, (gK i - δ)) ≤ ∑ i, g i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpoint i
  simpa [Finset.sum_sub_distrib] using hsum

theorem exists_diagonal_ge_of_trace
    {M : ℕ} (hM : 0 < M) (q : Fin M → ℝ) (a : ℝ)
    (htrace : (M : ℝ) * a ≤ ∑ i, q i) :
    ∃ i, a ≤ q i := by
  have hnonempty : (Finset.univ : Finset (Fin M)).Nonempty := by
    exact ⟨⟨0, hM⟩, Finset.mem_univ _⟩
  have hle : (∑ _i : Fin M, a) ≤ ∑ i : Fin M, q i := by
    simpa using htrace
  obtain ⟨i, _hi, hia⟩ := Finset.exists_le_of_sum_le hnonempty hle
  exact ⟨i, hia⟩

theorem finite_trace_certificate
    {M : ℕ} (hM : 0 < M)
    (g gK : Fin M → ℝ) (δ a : ℝ)
    (herr : ∀ i, |g i - gK i| ≤ δ)
    (hmargin : (M : ℝ) * a ≤ (∑ i, gK i) - (M : ℝ) * δ) :
    ∃ i, a ≤ g i := by
  have htail := trace_tail_lower g gK δ herr
  have htrace : (M : ℝ) * a ≤ ∑ i, g i := le_trans hmargin htail
  exact exists_diagonal_ge_of_trace hM g a htrace

theorem finite_trace_certificate_positive
    {M : ℕ} (hM : 0 < M)
    (g gK : Fin M → ℝ) (δ a : ℝ)
    (ha : 0 < a)
    (herr : ∀ i, |g i - gK i| ≤ δ)
    (hmargin : (M : ℝ) * a ≤ (∑ i, gK i) - (M : ℝ) * δ) :
    ∃ i, 0 < g i := by
  obtain ⟨i, hi⟩ := finite_trace_certificate hM g gK δ a herr hmargin
  exact ⟨i, lt_of_lt_of_le ha hi⟩

#print axioms trace_tail_lower
#print axioms exists_diagonal_ge_of_trace
#print axioms finite_trace_certificate
#print axioms finite_trace_certificate_positive

end YMFiniteOSWitnessCover
