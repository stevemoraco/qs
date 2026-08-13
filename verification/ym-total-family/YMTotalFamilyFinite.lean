import Mathlib

/-!
# Yang--Mills finite detected-spectrum common-exponent firewall

This file isolates the exact scalar obstruction behind the following finite
spectral argument: a mode of energy `E` detected with positive weight `A`
cannot obey an eventual upper bound with exponent `m > E`.

The first theorem produces a concrete certificate time. The second converts
an eventual bound into `m ≤ E`. The last theorem applies the scalar result to
every mode in a finite detected family. No continuum limit, transfer matrix,
Hamiltonian construction, or Yang--Mills existence theorem is formalized.
-/

namespace MillenniumBraid
namespace YMTotalFamilyFinite

open Filter

/-- If `A > 0`, `C ≥ 0`, and `E < m`, the explicit nonnegative time
`(C / A + 1) / (m - E)` makes the slower exponential strictly dominate. -/
theorem explicitCertificateTime
    (A C E m : ℝ)
    (hA : 0 < A)
    (hC : 0 ≤ C)
    (hEm : E < m) :
    let t := (C / A + 1) / (m - E)
    0 ≤ t ∧ C * Real.exp (-m * t) < A * Real.exp (-E * t) := by
  dsimp only
  have hgap : 0 < m - E := sub_pos.mpr hEm
  have hCA : 0 ≤ C / A := div_nonneg hC (le_of_lt hA)
  have ht : 0 ≤ (C / A + 1) / (m - E) :=
    div_nonneg (by linarith) (le_of_lt hgap)
  constructor
  · exact ht
  · have hlinear : C < A * (1 + (m - E) * ((C / A + 1) / (m - E))) := by
      field_simp
      nlinarith
    have hexpLower :
        1 + (m - E) * ((C / A + 1) / (m - E)) ≤
          Real.exp ((m - E) * ((C / A + 1) / (m - E))) := by
      simpa [add_comm] using
        Real.add_one_le_exp ((m - E) * ((C / A + 1) / (m - E)))
    have hscaled :
        C < A * Real.exp ((m - E) * ((C / A + 1) / (m - E))) :=
      lt_of_lt_of_le hlinear (mul_le_mul_of_nonneg_left hexpLower (le_of_lt hA))
    have hmul :=
      mul_lt_mul_of_pos_right hscaled
        (Real.exp_pos (-m * ((C / A + 1) / (m - E))))
    calc
      C * Real.exp (-m * ((C / A + 1) / (m - E))) <
          (A * Real.exp ((m - E) * ((C / A + 1) / (m - E)))) *
            Real.exp (-m * ((C / A + 1) / (m - E))) := hmul
      _ = A * Real.exp (-E * ((C / A + 1) / (m - E))) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 1
            ring

/-- A positive detected mode satisfying a common exponential upper bound at
all nonnegative times has energy at least the advertised exponent. -/
theorem detectedModeLowerBound
    (A C E m : ℝ)
    (hA : 0 < A)
    (hC : 0 ≤ C)
    (hdecay : ∀ t : ℝ, 0 ≤ t →
      A * Real.exp (-E * t) ≤ C * Real.exp (-m * t)) :
    m ≤ E := by
  by_contra hnot
  have hEm : E < m := lt_of_not_ge hnot
  obtain ⟨ht, hstrict⟩ := explicitCertificateTime A C E m hA hC hEm
  exact (not_lt_of_ge (hdecay _ ht)) hstrict

/-- Finite coverage plus a common detected decay exponent forces every listed
energy above that exponent. `weight i j > 0` is the exact finite form of the
statement that detector `i` sees mode `j`. -/
theorem finiteDetectedSpectrumLowerBound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (energy : κ → ℝ)
    (weight : ι → κ → ℝ)
    (C : ι → ℝ)
    (m : ℝ)
    (hC : ∀ i, 0 ≤ C i)
    (hcover : ∀ j, ∃ i, 0 < weight i j)
    (hdecay : ∀ i j t, 0 < weight i j → 0 ≤ t →
      weight i j * Real.exp (-energy j * t) ≤
        C i * Real.exp (-m * t)) :
    ∀ j, m ≤ energy j := by
  intro j
  obtain ⟨i, hweight⟩ := hcover j
  exact detectedModeLowerBound (weight i j) (C i) (energy j) m
    hweight (hC i) (fun t ht => hdecay i j t hweight ht)

#print axioms explicitCertificateTime
#print axioms detectedModeLowerBound
#print axioms finiteDetectedSpectrumLowerBound

end YMTotalFamilyFinite
end MillenniumBraid
