import Mathlib

open scoped BigOperators

namespace MillenniumBraid.PNPConditioningFinite

variable {C X : Type*} [Fintype C] [Fintype X]

def mixedError (mu : C → ℝ) (err : C → X → ℝ) (x : X) : ℝ :=
  ∑ c, mu c * err c x

def subfamilyMass (mu : C → ℝ) (p : C → Prop) [DecidablePred p] : ℝ :=
  ∑ c, if p c then mu c else 0

def restrictedWeight
    (mu : C → ℝ) (keep : C → Prop) [DecidablePred keep]
    (scale : ℝ) (c : C) : ℝ :=
  if keep c then scale * mu c else 0

theorem massSplit
    (mu : C → ℝ) (p : C → Prop) [DecidablePred p] :
    subfamilyMass mu p + subfamilyMass mu (fun c => ¬ p c) = ∑ c, mu c := by
  classical
  simp only [subfamilyMass]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : p c <;> simp [hc]

theorem complementMass
    (mu : C → ℝ) (bad : C → Prop) [DecidablePred bad]
    (hsum : ∑ c, mu c = 1) :
    subfamilyMass mu (fun c => ¬ bad c) = 1 - subfamilyMass mu bad := by
  have h := massSplit mu bad
  linarith

theorem restrictedWeight_sum
    (mu : C → ℝ) (keep : C → Prop) [DecidablePred keep]
    (scale : ℝ) :
    ∑ c, restrictedWeight mu keep scale c = scale * subfamilyMass mu keep := by
  classical
  simp only [restrictedWeight, subfamilyMass]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : keep c <;> simp [hc]

theorem restrictedWeight_sum_one
    (mu : C → ℝ) (keep : C → Prop) [DecidablePred keep]
    (scale : ℝ) (hnorm : scale * subfamilyMass mu keep = 1) :
    ∑ c, restrictedWeight mu keep scale c = 1 := by
  rw [restrictedWeight_sum]
  exact hnorm

theorem numerator_le
    (mu : C → ℝ) (err : C → X → ℝ)
    (keep : C → Prop) [DecidablePred keep]
    (hmu : ∀ c, 0 ≤ mu c)
    (h0 : ∀ c x, 0 ≤ err c x) :
    ∀ x, (∑ c, if keep c then mu c * err c x else 0) ≤ mixedError mu err x := by
  intro x
  simp only [mixedError]
  apply Finset.sum_le_sum
  intro c _
  by_cases hc : keep c
  · simp [hc]
  · simp only [hc, if_false]
    exact mul_nonneg (hmu c) (h0 c x)

theorem restrictedMixedError_eq
    (mu : C → ℝ) (err : C → X → ℝ)
    (keep : C → Prop) [DecidablePred keep]
    (scale : ℝ) (x : X) :
    mixedError (restrictedWeight mu keep scale) err x =
      scale * (∑ c, if keep c then mu c * err c x else 0) := by
  classical
  simp only [mixedError, restrictedWeight]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : keep c <;> simp [hc]
  ring

theorem pointwiseAfterRestriction
    (mu : C → ℝ) (err : C → X → ℝ)
    (keep : C → Prop) [DecidablePred keep]
    (scale epsilon : ℝ)
    (hscale : 0 ≤ scale)
    (hmu : ∀ c, 0 ≤ mu c)
    (h0 : ∀ c x, 0 ≤ err c x)
    (hp : ∀ x, mixedError mu err x ≤ epsilon) :
    ∀ x, mixedError (restrictedWeight mu keep scale) err x ≤ scale * epsilon := by
  intro x
  rw [restrictedMixedError_eq]
  have hn := numerator_le mu err keep hmu h0 x
  have hne : (∑ c, if keep c then mu c * err c x else 0) ≤ epsilon :=
    hn.trans (hp x)
  exact mul_le_mul_of_nonneg_left hne hscale

theorem restrictedWeight_nonneg
    (mu : C → ℝ) (keep : C → Prop) [DecidablePred keep]
    (scale : ℝ) (hs : 0 ≤ scale) (hm : ∀ c, 0 ≤ mu c) :
    ∀ c, 0 ≤ restrictedWeight mu keep scale c := by
  intro c
  by_cases hc : keep c
  · simp [restrictedWeight, hc, mul_nonneg hs (hm c)]
  · simp [restrictedWeight, hc]

#print axioms massSplit
#print axioms complementMass
#print axioms restrictedWeight_sum
#print axioms restrictedWeight_sum_one
#print axioms numerator_le
#print axioms restrictedMixedError_eq
#print axioms pointwiseAfterRestriction
#print axioms restrictedWeight_nonneg

end MillenniumBraid.PNPConditioningFinite
