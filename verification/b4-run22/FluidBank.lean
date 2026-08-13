import Mathlib

namespace B4.Run22.Fluid

theorem banker_relay_closure
    {A B W Z Dy Dz c : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hZ : Z ≠ 0) (hc : c ≠ 0)
    (hDiff : A * W + B * Z = 0)
    (hExtP : Dy * Z = 2 * A * Dz * c)
    (hExtQ : Dy * W = 2 * B * Dz * c) :
    Dy = 0 ∧ Dz = 0 := by
  have hsum : A * (Dy * W) + B * (Dy * Z) = 0 := by
    calc
      A * (Dy * W) + B * (Dy * Z) = Dy * (A * W + B * Z) := by ring
      _ = 0 := by rw [hDiff]; ring
  have hprod : 4 * A * B * Dz * c = 0 := by
    calc
      4 * A * B * Dz * c = A * (2 * B * Dz * c) + B * (2 * A * Dz * c) := by ring
      _ = A * (Dy * W) + B * (Dy * Z) := by rw [← hExtQ, ← hExtP]
      _ = 0 := hsum
  have hprod' : (4 * A * B * c) * Dz = 0 := by
    calc
      (4 * A * B * c) * Dz = 4 * A * B * Dz * c := by ring
      _ = 0 := hprod
  have hcoef : 4 * A * B * c ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hA) hB) hc
  have hDz : Dz = 0 := (mul_eq_zero.mp hprod').resolve_left hcoef
  have hDyZ : Dy * Z = 0 := by
    calc
      Dy * Z = 2 * A * Dz * c := hExtP
      _ = 0 := by rw [hDz]; ring
  have hDy : Dy = 0 := (mul_eq_zero.mp hDyZ).resolve_right hZ
  exact ⟨hDy, hDz⟩

theorem critic_degenerate_second_factor_has_nonzero_witness :
    let A : ℝ := 1
    let B : ℝ := 0
    let W : ℝ := 0
    let Z : ℝ := 1
    let Dy : ℝ := 2
    let Dz : ℝ := 1
    let c : ℝ := 1
    A ≠ 0 ∧ Z ≠ 0 ∧ c ≠ 0 ∧
      A * W + B * Z = 0 ∧
      Dy * Z = 2 * A * Dz * c ∧
      Dy * W = 2 * B * Dz * c ∧
      (Dy ≠ 0 ∨ Dz ≠ 0) := by
  norm_num

theorem cleaner_nonzero_pair_incompatible
    {A B W Z Dy Dz c : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hZ : Z ≠ 0) (hc : c ≠ 0)
    (hNonzero : Dy ≠ 0 ∨ Dz ≠ 0)
    (hDiff : A * W + B * Z = 0)
    (hExtP : Dy * Z = 2 * A * Dz * c)
    (hExtQ : Dy * W = 2 * B * Dz * c) :
    False := by
  obtain ⟨hDy, hDz⟩ := banker_relay_closure hA hB hZ hc hDiff hExtP hExtQ
  rcases hNonzero with h | h
  · exact h hDy
  · exact h hDz

#print axioms banker_relay_closure
#print axioms critic_degenerate_second_factor_has_nonzero_witness
#print axioms cleaner_nonzero_pair_incompatible

end B4.Run22.Fluid
