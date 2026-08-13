import Mathlib

/-!
# RH B54 Q=420 finite certificate and relaxed-pair algebra

This file formalizes only finite arithmetic and the scalar pair inequality used
in the relaxed Landau variational bound. It does not formalize the entropy-area
integral identity, infinite series, Stirling, the prime-number transfer,
Johnston's criterion, or the Riemann hypothesis.
-/

namespace Millennium.RH.B54Q420Finite

/-- The exact Q=420 Landau cell value on the common 420-cell grid. -/
def q420Landau (k : ℕ) : ℤ :=
  ((420 * k / 420 : ℕ) : ℤ)
    + ((105 * k / 420 : ℕ) : ℤ)
    + ((70 * k / 420 : ℕ) : ℤ)
    + ((42 * k / 420 : ℕ) : ℤ)
    + ((30 * k / 420 : ℕ) : ℤ)
    + ((20 * k / 420 : ℕ) : ℤ)
    - ((210 * k / 420 : ℕ) : ℤ)
    - ((210 * k / 420 : ℕ) : ℤ)
    - ((140 * k / 420 : ℕ) : ℤ)
    - ((35 * k / 420 : ℕ) : ℤ)
    - ((60 * k / 420 : ℕ) : ℤ)
    - ((21 * k / 420 : ℕ) : ℤ)
    - ((10 * k / 420 : ℕ) : ℤ)
    - ((k / 420 : ℕ) : ℤ)

/-- The scaled height-one Chebyshev core on the same grid. -/
def q420Core (k : ℕ) : ℤ :=
  ((420 * k / 420 : ℕ) : ℤ)
    + ((105 * k / 420 : ℕ) : ℤ)
    + ((70 * k / 420 : ℕ) : ℤ)
    - ((210 * k / 420 : ℕ) : ℤ)
    - ((210 * k / 420 : ℕ) : ℤ)
    - ((140 * k / 420 : ℕ) : ℤ)
    - ((35 * k / 420 : ℕ) : ℤ)

/-- The entropy-lowering signed perturbation on the same grid. -/
def q420Perturbation (k : ℕ) : ℤ :=
  ((42 * k / 420 : ℕ) : ℤ)
    + ((30 * k / 420 : ℕ) : ℤ)
    + ((20 * k / 420 : ℕ) : ℤ)
    - ((60 * k / 420 : ℕ) : ℤ)
    - ((21 * k / 420 : ℕ) : ℤ)
    - ((10 * k / 420 : ℕ) : ℤ)
    - ((k / 420 : ℕ) : ℤ)

/-- Reflection on the complete residue grid. -/
def reflect420 (k : Fin 420) : Fin 420 :=
  ⟨419 - k.1, by omega⟩

/-- Exact balance of the numerator and denominator coefficient lists. -/
theorem q420_balance :
    420 + 105 + 70 + 42 + 30 + 20 =
      210 + 210 + 140 + 35 + 60 + 21 + 10 + 1 := by
  norm_num

/-- Exact height: eight denominator entries versus six numerator entries. -/
theorem q420_height : (8 : ℤ) - 6 = 2 := by
  norm_num

/-- The total Landau cell is exactly core plus perturbation. -/
theorem q420_eq_core_add_perturbation (k : ℕ) :
    q420Landau k = q420Core k + q420Perturbation k := by
  simp [q420Landau, q420Core, q420Perturbation]
  ring

/-- Every one of the 420 exact half-open cells has value 0, 1, or 2. -/
theorem q420_landau_bounds :
    ∀ k : Fin 420, 0 ≤ q420Landau k.1 ∧ q420Landau k.1 ≤ 2 := by
  decide

/-- Exact height-two reflection on every cell. -/
theorem q420_reflection :
    ∀ k : Fin 420,
      q420Landau k.1 + q420Landau (reflect420 k).1 = 2 := by
  decide

/-- The complete dyadic coverage cell `[1/420,2/420)` has value one. -/
theorem q420_dyadic_coverage : q420Landau 1 = 1 := by
  norm_num [q420Landau]

/-- Every negative perturbation cell is absorbed by a core-one cell. -/
theorem q420_negative_defects_are_covered :
    ∀ k : Fin 420, q420Perturbation k.1 = -1 → q420Core k.1 = 1 := by
  decide

/-- Every perturbation-two cell lies under a core-zero cell. -/
theorem q420_positive_twos_are_covered :
    ∀ k : Fin 420, q420Perturbation k.1 = 2 → q420Core k.1 = 0 := by
  decide

/-- Exact distribution count for the zero cells. -/
theorem q420_zero_count :
    ((Finset.univ : Finset (Fin 420)).filter
      (fun k => q420Landau k.1 = 0)).card = 100 := by
  decide

/-- Exact distribution count for the one cells. -/
theorem q420_one_count :
    ((Finset.univ : Finset (Fin 420)).filter
      (fun k => q420Landau k.1 = 1)).card = 220 := by
  decide

/-- Exact distribution count for the two cells. -/
theorem q420_two_count :
    ((Finset.univ : Finset (Fin 420)).filter
      (fun k => q420Landau k.1 = 2)).card = 100 := by
  decide

/-- The exact integer inequality equivalent to `C_420 < C_336`. -/
theorem q420_beats_q336_integer_certificate :
    2 ^ 158 * 3 ^ 84 * 7 ^ 84 < 5 ^ 80 * 17 ^ 85 := by
  norm_num

/-- The affine continuation to k=6 fails at x=251/12600. -/
theorem affine_k6_counterexample :
    (((504 * 251 / 12600 : ℕ) : ℤ)
      + ((126 * 251 / 12600 : ℕ) : ℤ)
      + ((84 * 251 / 12600 : ℕ) : ℤ)
      + ((50 * 251 / 12600 : ℕ) : ℤ)
      + ((36 * 251 / 12600 : ℕ) : ℤ)
      + ((24 * 251 / 12600 : ℕ) : ℤ)
      - ((252 * 251 / 12600 : ℕ) : ℤ)
      - ((252 * 251 / 12600 : ℕ) : ℤ)
      - ((168 * 251 / 12600 : ℕ) : ℤ)
      - ((42 * 251 / 12600 : ℕ) : ℤ)
      - ((72 * 251 / 12600 : ℕ) : ℤ)
      - ((25 * 251 / 12600 : ℕ) : ℤ)
      - ((12 * 251 / 12600 : ℕ) : ℤ)
      - ((251 / 12600 : ℕ) : ℤ)) = -1 := by
  norm_num

/-- Scalar core of the reflected-pair minimization: if the left weight is at
least the reflected right weight and the left mass is nonnegative, then the
pair is bounded below by putting zero mass on the left. -/
theorem reflected_pair_lower
    (g wLeft wRight : ℝ)
    (hg : 0 ≤ g)
    (hweight : wRight ≤ wLeft) :
    2 * wRight ≤ g * wLeft + (2 - g) * wRight := by
  have hprod : 0 ≤ g * (wLeft - wRight) :=
    mul_nonneg hg (sub_nonneg.mpr hweight)
  nlinarith

/-- On a mandatory unit-mass cell, the reflected pair contributes exactly the
sum of the two weights. -/
theorem mandatory_pair_identity (wLeft wRight : ℝ) :
    (1 : ℝ) * wLeft + (2 - 1) * wRight = wLeft + wRight := by
  ring

/-- Finite-sum shadow of the sharp relaxed lower bound. Required cells pay
an extra left-minus-right weight; all other cells pay only the reflected
baseline. -/
theorem finite_reflected_weight_lower
    {ι : Type*} [DecidableEq ι]
    (s required : Finset ι)
    (g wLeft wRight : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i)
    (hweight : ∀ i ∈ s, wRight i ≤ wLeft i)
    (hrequired : ∀ i ∈ required, g i = 1) :
    ∑ i ∈ s,
        (2 * wRight i +
          if i ∈ required then wLeft i - wRight i else 0) ≤
      ∑ i ∈ s, (g i * wLeft i + (2 - g i) * wRight i) := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hir : i ∈ required
  · simp only [hir, if_true, hrequired i hir]
    ring_nf
  · simp only [hir, if_false, add_zero]
    exact reflected_pair_lower (g i) (wLeft i) (wRight i)
      (hg i hi) (hweight i hi)

#print axioms q420_balance
#print axioms q420_height
#print axioms q420_eq_core_add_perturbation
#print axioms q420_landau_bounds
#print axioms q420_reflection
#print axioms q420_dyadic_coverage
#print axioms q420_negative_defects_are_covered
#print axioms q420_positive_twos_are_covered
#print axioms q420_zero_count
#print axioms q420_one_count
#print axioms q420_two_count
#print axioms q420_beats_q336_integer_certificate
#print axioms affine_k6_counterexample
#print axioms reflected_pair_lower
#print axioms mandatory_pair_identity
#print axioms finite_reflected_weight_lower

end Millennium.RH.B54Q420Finite
