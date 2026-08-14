import Mathlib

/-!
# Signed Yu work orientation firewall

Finite weighted real algebra only. A signed scalar coefficient can be absorbed
into the orientation of a bounded angular observable while its absolute value
becomes a nonnegative total-variation weight. Consequently a positive signed
mean still forces quantitative total-variation mass in an oriented visible
sector.

This file does **not** formalize Yu's PDE work density, integrability, amplitude
truncation, tightness, Young measures, recurrence, Navier--Stokes regularity,
or blow-up.
-/

open scoped BigOperators

noncomputable section

namespace NSYuSignedWorkOrientation

variable {ι : Type*} [Fintype ι]

/-- Orient the observable by the sign of its scalar work coefficient. -/
def orientedObservable (c k : ι → ℝ) (i : ι) : ℝ :=
  if 0 ≤ c i then k i else -k i

/-- Total variation carried by the oriented sector above `κ`. -/
def orientedVisibleWeight (c k : ι → ℝ) (κ : ℝ) : ℝ :=
  ∑ i, if κ < orientedObservable c k i then |c i| else 0

omit [Fintype ι] in
/-- Pointwise polar decomposition over the reals. -/
theorem abs_mul_orientedObservable
    (c k : ι → ℝ) (i : ι) :
    |c i| * orientedObservable c k i = c i * k i := by
  by_cases hi : 0 ≤ c i
  · rw [orientedObservable, if_pos hi, abs_of_nonneg hi]
  · have hic : c i < 0 := lt_of_not_ge hi
    rw [orientedObservable, if_neg hi, abs_of_neg hic]
    ring

/-- The signed work sum equals a nonnegative-total-variation weighted oriented
observable sum. -/
theorem signed_work_eq_totalVariation_oriented
    (c k : ι → ℝ) :
    (∑ i, c i * k i) =
      ∑ i, |c i| * orientedObservable c k i := by
  apply Finset.sum_congr rfl
  intro i _hi
  exact (abs_mul_orientedObservable c k i).symm

omit [Fintype ι] in
/-- An absolute bound on the original angular observable survives orientation. -/
theorem orientedObservable_le_of_abs_le
    (c k : ι → ℝ) (M : ℝ)
    (hk : ∀ i, |k i| ≤ M) (i : ι) :
    orientedObservable c k i ≤ M := by
  by_cases hi : 0 ≤ c i
  · rw [orientedObservable, if_pos hi]
    exact (le_abs_self (k i)).trans (hk i)
  · rw [orientedObservable, if_neg hi]
    exact (neg_le_abs (k i)).trans (hk i)

/-- A positive signed mean relative to total variation forces oriented visible
mass. No positivity of the original coefficients is required. -/
theorem signed_mean_forces_oriented_visible_mass
    (c k : ι → ℝ) (κ α M : ℝ)
    (hk : ∀ i, |k i| ≤ M)
    (hmean : α * (∑ i, |c i|) ≤ ∑ i, c i * k i) :
    (α - κ) * (∑ i, |c i|) ≤
      (M - κ) * orientedVisibleWeight c k κ := by
  have hmean' :
      α * (∑ i, |c i|) ≤
        ∑ i, |c i| * orientedObservable c k i := by
    calc
      α * (∑ i, |c i|) ≤ ∑ i, c i * k i := hmean
      _ = ∑ i, |c i| * orientedObservable c k i :=
        signed_work_eq_totalVariation_oriented c k
  have hpoint : ∀ i,
      |c i| * orientedObservable c k i ≤
        κ * |c i| + (M - κ) *
          (if κ < orientedObservable c k i then |c i| else 0) := by
    intro i
    by_cases hi : κ < orientedObservable c k i
    · simp only [hi, if_true]
      have hmul := mul_le_mul_of_nonneg_left
        (orientedObservable_le_of_abs_le c k M hk i) (abs_nonneg (c i))
      nlinarith
    · have hik : orientedObservable c k i ≤ κ := le_of_not_gt hi
      simp only [hi, if_false, mul_zero, add_zero]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left hik (abs_nonneg (c i))
  have hupper :
      (∑ i, |c i| * orientedObservable c k i) ≤
        κ * (∑ i, |c i|) +
          (M - κ) * orientedVisibleWeight c k κ := by
    calc
      (∑ i, |c i| * orientedObservable c k i) ≤
          ∑ i, (κ * |c i| + (M - κ) *
            (if κ < orientedObservable c k i then |c i| else 0)) := by
        exact Finset.sum_le_sum (fun i _hi => hpoint i)
      _ = κ * (∑ i, |c i|) +
          (M - κ) * orientedVisibleWeight c k κ := by
        unfold orientedVisibleWeight
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  linarith

/-- Strictly positive signed mean above `κ` forces strictly positive oriented
total-variation mass. -/
theorem positive_signed_mean_forces_positive_oriented_mass
    (c k : ι → ℝ) (κ α M : ℝ)
    (hk : ∀ i, |k i| ≤ M)
    (hκM : κ < M)
    (hκα : κ < α)
    (htv : 0 < ∑ i, |c i|)
    (hmean : α * (∑ i, |c i|) ≤ ∑ i, c i * k i) :
    0 < orientedVisibleWeight c k κ := by
  have hmass := signed_mean_forces_oriented_visible_mass
    c k κ α M hk hmean
  have hleft : 0 < (α - κ) * (∑ i, |c i|) :=
    mul_pos (sub_pos.mpr hκα) htv
  by_contra hnot
  have hveryle : orientedVisibleWeight c k κ ≤ 0 := le_of_not_gt hnot
  have hright : (M - κ) * orientedVisibleWeight c k κ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hκM.le) hveryle
  linarith

/-- A negative coefficient flips which angular sign is work-visible. -/
theorem negative_coefficient_flips_orientation
    (k : ℝ) :
    orientedObservable (fun _ : Unit => (-1 : ℝ)) (fun _ => k) () = -k := by
  simp [orientedObservable]

#print axioms orientedObservable
#print axioms orientedVisibleWeight
#print axioms abs_mul_orientedObservable
#print axioms signed_work_eq_totalVariation_oriented
#print axioms orientedObservable_le_of_abs_le
#print axioms signed_mean_forces_oriented_visible_mass
#print axioms positive_signed_mean_forces_positive_oriented_mass
#print axioms negative_coefficient_flips_orientation

end NSYuSignedWorkOrientation
