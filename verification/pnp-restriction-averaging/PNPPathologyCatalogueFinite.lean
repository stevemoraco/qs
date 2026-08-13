import Mathlib

open scoped BigOperators

namespace MillenniumBraid.PNPPathologyCatalogueFinite

variable {C X : Type*} [Fintype C] [Fintype X]

def mixedError (mu : C → ℝ) (err : C → X → ℝ) (x : X) : ℝ :=
  ∑ c, mu c * err c x

def subfamilyMass (mu : C → ℝ) (p : C → Prop) [DecidablePred p] : ℝ :=
  ∑ c, if p c then mu c else 0

theorem rowFloor
    (err : C → X → ℝ) (K : Finset X) (bad : C → Prop)
    (h0 : ∀ c x, 0 ≤ err c x)
    (hw : ∀ c, bad c → ∃ x ∈ K, 1 ≤ err c x) :
    ∀ c, bad c → 1 ≤ ∑ x in K, err c x := by
  intro c hc
  obtain ⟨x, hxK, hx⟩ := hw c hc
  have hs : err c x ≤ ∑ y in K, err c y := by
    exact Finset.single_le_sum (fun y _ => h0 c y) hxK
  exact hx.trans hs

theorem fubini
    (mu : C → ℝ) (err : C → X → ℝ) (K : Finset X) :
    ∑ c, mu c * (∑ x in K, err c x) =
      ∑ x in K, mixedError mu err x := by
  calc
    ∑ c, mu c * (∑ x in K, err c x)
        = ∑ c, ∑ x in K, mu c * err c x := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
    _ = ∑ x in K, ∑ c, mu c * err c x := by
          rw [Finset.sum_comm]
    _ = ∑ x in K, mixedError mu err x := by rfl

theorem massBound
    (mu : C → ℝ) (err : C → X → ℝ) (K : Finset X)
    (bad : C → Prop) [DecidablePred bad] (epsilon : ℝ)
    (hmu : ∀ c, 0 ≤ mu c)
    (h0 : ∀ c x, 0 ≤ err c x)
    (hw : ∀ c, bad c → ∃ x ∈ K, 1 ≤ err c x)
    (hp : ∀ x ∈ K, mixedError mu err x ≤ epsilon) :
    subfamilyMass mu bad ≤ (K.card : ℝ) * epsilon := by
  have hr := rowFloor err K bad h0 hw
  have ht : ∀ c,
      (if bad c then mu c else 0) ≤ mu c * (∑ x in K, err c x) := by
    intro c
    by_cases hc : bad c
    · simp only [hc, if_true]
      exact mul_le_mul_of_nonneg_left (hr c hc) (hmu c)
    · simp only [hc, if_false]
      exact mul_nonneg (hmu c) (Finset.sum_nonneg (fun x _ => h0 c x))
  calc
    subfamilyMass mu bad ≤ ∑ c, mu c * (∑ x in K, err c x) := by
      simp only [subfamilyMass]
      exact Finset.sum_le_sum (fun c _ => ht c)
    _ = ∑ x in K, mixedError mu err x := fubini mu err K
    _ ≤ ∑ _x in K, epsilon := by
      exact Finset.sum_le_sum (fun x hx => hp x hx)
    _ = (K.card : ℝ) * epsilon := by simp

#print axioms rowFloor
#print axioms fubini
#print axioms massBound

end MillenniumBraid.PNPPathologyCatalogueFinite
