import Mathlib

/-!
# RH run 17 dyadic Gumbel block — finite core

HONESTY BOUNDARY:
This file formalizes only finite algebra/order statements used by the dyadic
block reduction. It does not define zeta, prime sums, Gumbel integrals, RH, or
the analytic depth equivalence.
-/

namespace MillenniumRun17
namespace RHDyadicBlock

/-- Polynomial geometric telescoping, stated without division. -/
lemma one_sub_mul_geom_sum (r : ℝ) : ∀ n : ℕ,
    (1 - r) * (Finset.sum (Finset.range n) fun k => r ^ k) = 1 - r ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

/-- Exact finite geometric identity behind the dyadic block kernel. -/
theorem geometric_block_identity (r : ℝ) (D : ℕ) :
    (1 - r) *
        (Finset.sum (Finset.range (D + 1)) fun k => r ^ (D + k)) =
      r ^ D - r ^ (2 * D + 1) := by
  have hsum :
      (Finset.sum (Finset.range (D + 1)) fun k => r ^ (D + k)) =
        r ^ D * (Finset.sum (Finset.range (D + 1)) fun k => r ^ k) := by
    calc
      (Finset.sum (Finset.range (D + 1)) fun k => r ^ (D + k)) =
          Finset.sum (Finset.range (D + 1)) (fun k => r ^ D * r ^ k) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [pow_add]
      _ = r ^ D * (Finset.sum (Finset.range (D + 1)) fun k => r ^ k) := by
            rw [Finset.mul_sum]
  rw [hsum]
  calc
    (1 - r) *
        (r ^ D * (Finset.sum (Finset.range (D + 1)) fun k => r ^ k)) =
        r ^ D *
          ((1 - r) * (Finset.sum (Finset.range (D + 1)) fun k => r ^ k)) := by
            ring
    _ = r ^ D * (1 - r ^ (D + 1)) := by
      rw [one_sub_mul_geom_sum]
    _ = r ^ D - r ^ (D + (D + 1)) := by
      rw [mul_sub, mul_one, ← pow_add]
    _ = r ^ D - r ^ (2 * D + 1) := by
      congr 2 <;> omega

/-- The dyadic block kernel is nonnegative on `0 ≤ r ≤ 1`. -/
theorem block_kernel_nonneg (r : ℝ) (D : ℕ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ r ^ D - r ^ (2 * D + 1) := by
  have hpowD : 0 ≤ r ^ D := pow_nonneg hr0 D
  have hpowTail : r ^ (D + 1) ≤ 1 := pow_le_one₀ hr0 hr1
  have hmul : r ^ D * r ^ (D + 1) ≤ r ^ D * 1 :=
    mul_le_mul_of_nonneg_left hpowTail hpowD
  have hexp : r ^ D * r ^ (D + 1) = r ^ (2 * D + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hexp] at hmul
  simpa using hmul

/-- A dyadic block sum of an antitone sequence is bounded below by its right
endpoint times the number of terms. -/
theorem antitone_block_lower (B : ℕ → ℝ) (hanti : Antitone B) (D : ℕ) :
    (D + 1 : ℝ) * B (2 * D) ≤
      Finset.sum (Finset.range (D + 1)) (fun k => B (D + k)) := by
  calc
    (D + 1 : ℝ) * B (2 * D) =
        Finset.sum (Finset.range (D + 1)) (fun _ => B (2 * D)) := by simp
    _ ≤ Finset.sum (Finset.range (D + 1)) (fun k => B (D + k)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply hanti
      have hk' : k < D + 1 := Finset.mem_range.mp hk
      omega

/-- A dyadic block sum of an antitone sequence is bounded above by its left
endpoint times the number of terms. -/
theorem antitone_block_upper (B : ℕ → ℝ) (hanti : Antitone B) (D : ℕ) :
    Finset.sum (Finset.range (D + 1)) (fun k => B (D + k)) ≤
      (D + 1 : ℝ) * B D := by
  calc
    Finset.sum (Finset.range (D + 1)) (fun k => B (D + k)) ≤
        Finset.sum (Finset.range (D + 1)) (fun _ => B D) := by
      apply Finset.sum_le_sum
      intro k hk
      apply hanti
      omega
    _ = (D + 1 : ℝ) * B D := by simp

/-- Finite dense-scale interpolation: an antitone nonnegative sequence can be
controlled between two certified scales without a quantifier swap. -/
theorem dense_scale_interpolation
    (B : ℕ → ℝ) (hanti : Antitone B)
    {D d E : ℕ} (hDd : D ≤ d) (hdE : d ≤ E) (hBD : 0 ≤ B D) :
    (d : ℝ) * B d ≤ (E : ℝ) * B D := by
  calc
    (d : ℝ) * B d ≤ (d : ℝ) * B D :=
      mul_le_mul_of_nonneg_left (hanti hDd) (Nat.cast_nonneg d)
    _ ≤ (E : ℝ) * B D := by
      apply mul_le_mul_of_nonneg_right _ hBD
      exact_mod_cast hdE

#print axioms MillenniumRun17.RHDyadicBlock.one_sub_mul_geom_sum
#print axioms MillenniumRun17.RHDyadicBlock.geometric_block_identity
#print axioms MillenniumRun17.RHDyadicBlock.block_kernel_nonneg
#print axioms MillenniumRun17.RHDyadicBlock.antitone_block_lower
#print axioms MillenniumRun17.RHDyadicBlock.antitone_block_upper
#print axioms MillenniumRun17.RHDyadicBlock.dense_scale_interpolation

end RHDyadicBlock
end MillenniumRun17
