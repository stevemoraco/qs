import Mathlib

namespace Millennium.YangMills

/-!
Finite scalar repair for the fixed-order marked recursion in the enlarged-ball
version of Kirk v4 Lemma 6.38.  No Yang--Mills geometry or Clay conclusion is
encoded here.
-/

/-- One affine step stays in a prescribed ball. -/
theorem affine_step_preserves_ball
    (q C M x : ℝ)
    (hq : 0 ≤ q)
    (hx : x ≤ M)
    (hC : C ≤ (1 - q) * M) :
    q * x + C ≤ M := by
  have hqx : q * x ≤ q * M := mul_le_mul_of_nonneg_left hx hq
  nlinarith

/-- Explicit invariant radius for contraction `q` and forcing `C`. -/
noncomputable def explicitForcingRadius (q C : ℝ) : ℝ :=
  C / (1 - q) + 1

/-- The explicit radius pays the forcing budget. -/
theorem forcing_budget_at_explicit_radius
    (q C : ℝ)
    (hq : q < 1)
    (hC : 0 ≤ C) :
    C ≤ (1 - q) * explicitForcingRadius q C := by
  have hd : 0 < 1 - q := sub_pos.mpr hq
  have hne : 1 - q ≠ 0 := ne_of_gt hd
  have hcalc :
      (1 - q) * explicitForcingRadius q C = C + (1 - q) := by
    unfold explicitForcingRadius
    field_simp [hne]
  rw [hcalc]
  linarith

/-- The explicit radius is positive. -/
theorem explicitForcingRadius_pos
    (q C : ℝ)
    (hq : q < 1)
    (hC : 0 ≤ C) :
    0 < explicitForcingRadius q C := by
  have hd : 0 < 1 - q := sub_pos.mpr hq
  unfold explicitForcingRadius
  have hdiv : 0 ≤ C / (1 - q) := div_nonneg hC (le_of_lt hd)
  linarith

/--
A lower-triangular family of affine marked recurrences stays in its prescribed
coefficient balls.  Lower-order forcing may depend on all lower mark orders at
the current recursion depth.
-/
theorem triangular_affine_forcing_bounded
    (x forcing : ℕ → ℕ → ℝ)
    (q : ℝ)
    (C M : ℕ → ℝ)
    (hq : 0 ≤ q)
    (hinit : ∀ k : ℕ, x k 0 ≤ M k)
    (hforcing : ∀ k n : ℕ,
      (∀ i : ℕ, i < k → x i n ≤ M i) → forcing k n ≤ C k)
    (hbudget : ∀ k : ℕ, C k ≤ (1 - q) * M k)
    (hrec : ∀ k n : ℕ,
      x k (n + 1) ≤ q * x k n + forcing k n) :
    ∀ k n : ℕ, x k n ≤ M k := by
  intro k n
  induction n generalizing k with
  | zero =>
      exact hinit k
  | succ n ih =>
      have hforce : forcing k n ≤ C k := by
        apply hforcing k n
        intro i _hi
        exact ih i
      have hreplace :
          q * x k n + forcing k n ≤ q * x k n + C k := by
        nlinarith
      have hball : q * x k n + C k ≤ M k :=
        affine_step_preserves_ball q (C k) (M k) (x k n)
          hq (ih k) (hbudget k)
      exact (hrec k n).trans (hreplace.trans hball)

/-- Concrete all-order bound using the explicit forcing radii. -/
theorem triangular_affine_forcing_explicit_bounded
    (x forcing : ℕ → ℕ → ℝ)
    (q : ℝ)
    (C : ℕ → ℝ)
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (hC : ∀ k : ℕ, 0 ≤ C k)
    (hinit : ∀ k : ℕ,
      x k 0 ≤ explicitForcingRadius q (C k))
    (hforcing : ∀ k n : ℕ,
      (∀ i : ℕ, i < k →
        x i n ≤ explicitForcingRadius q (C i)) →
      forcing k n ≤ C k)
    (hrec : ∀ k n : ℕ,
      x k (n + 1) ≤ q * x k n + forcing k n) :
    ∀ k n : ℕ,
      x k n ≤ explicitForcingRadius q (C k) := by
  apply triangular_affine_forcing_bounded
    x forcing q C (fun k => explicitForcingRadius q (C k)) hq0 hinit
  · exact hforcing
  · intro k
    exact forcing_budget_at_explicit_radius q (C k) hq1 (hC k)
  · exact hrec

#print axioms affine_step_preserves_ball
#print axioms forcing_budget_at_explicit_radius
#print axioms explicitForcingRadius_pos
#print axioms triangular_affine_forcing_bounded
#print axioms triangular_affine_forcing_explicit_bounded

end Millennium.YangMills
