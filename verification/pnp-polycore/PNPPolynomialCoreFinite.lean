import Mathlib

open scoped BigOperators

/-!
# P versus NP: finite polynomial-common-core transfer

This file formalizes only the finite weighted averaging statement behind the
observation that a fractional error core of total mass `T` forces pointwise
mixed error at least `1 / T` somewhere.

It does **not** define Boolean circuits, `B₂`, P, NP, hardness magnification,
asymptotics, or P versus NP.
-/

namespace MillenniumBraid
namespace PNPPolynomialCoreFinite

variable {C X : Type*} [Fintype C] [Fintype X]

/-- Pointwise error of a distribution `μ` over deterministic objects. -/
def mixedError (μ : C → ℝ) (err : C → X → ℝ) (x : X) : ℝ :=
  ∑ c, μ c * err c x

/-- Finite Fubini identity for a weighted error core. -/
theorem weightedErrorFubini
    (μ : C → ℝ) (w : X → ℝ) (err : C → X → ℝ) :
    ∑ c, μ c * (∑ x, w x * err c x)
      = ∑ x, w x * mixedError μ err x := by
  calc
    ∑ c, μ c * (∑ x, w x * err c x)
        = ∑ c, ∑ x, μ c * (w x * err c x) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
    _ = ∑ x, ∑ c, μ c * (w x * err c x) := by
          rw [Finset.sum_comm]
    _ = ∑ x, w x * (∑ c, μ c * err c x) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _
          ring
    _ = ∑ x, w x * mixedError μ err x := by
          rfl

/--
If every deterministic object incurs weighted core error at least one, then
any normalized nonnegative mixture has weighted expected error at least one.
-/
theorem fractionalCoreAverageFloor
    (μ : C → ℝ) (w : X → ℝ) (err : C → X → ℝ)
    (hμ : ∀ c, 0 ≤ μ c)
    (hμsum : ∑ c, μ c = 1)
    (hedge : ∀ c, 1 ≤ ∑ x, w x * err c x) :
    1 ≤ ∑ x, w x * mixedError μ err x := by
  calc
    1 = ∑ c, μ c := hμsum.symm
    _ ≤ ∑ c, μ c * (∑ x, w x * err c x) := by
          apply Finset.sum_le_sum
          intro c _
          have hc := mul_le_mul_of_nonneg_left (hedge c) (hμ c)
          simpa using hc
    _ = ∑ x, w x * mixedError μ err x :=
          weightedErrorFubini μ w err

/--
If every point has mixed error at most `ε`, a fractional core of total mass
`T = ∑ x, w x` forces `1 ≤ T * ε`.
-/
theorem fractionalCorePointwiseFloor
    (μ : C → ℝ) (w : X → ℝ) (err : C → X → ℝ) (ε : ℝ)
    (hμ : ∀ c, 0 ≤ μ c)
    (hμsum : ∑ c, μ c = 1)
    (hw : ∀ x, 0 ≤ w x)
    (hedge : ∀ c, 1 ≤ ∑ x, w x * err c x)
    (hpoint : ∀ x, mixedError μ err x ≤ ε) :
    1 ≤ (∑ x, w x) * ε := by
  calc
    1 ≤ ∑ x, w x * mixedError μ err x :=
      fractionalCoreAverageFloor μ w err hμ hμsum hedge
    _ ≤ ∑ x, w x * ε := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (hpoint x) (hw x)
    _ = (∑ x, w x) * ε := by
      rw [Finset.sum_mul]

/-- A pointwise error target strictly below the reciprocal core scale is impossible. -/
theorem noPointwiseBelowFractionalCore
    (μ : C → ℝ) (w : X → ℝ) (err : C → X → ℝ) (ε : ℝ)
    (hμ : ∀ c, 0 ≤ μ c)
    (hμsum : ∑ c, μ c = 1)
    (hw : ∀ x, 0 ≤ w x)
    (hedge : ∀ c, 1 ≤ ∑ x, w x * err c x)
    (hpoint : ∀ x, mixedError μ err x ≤ ε)
    (hsmall : (∑ x, w x) * ε < 1) : False := by
  have hfloor := fractionalCorePointwiseFloor μ w err ε hμ hμsum hw hedge hpoint
  linarith

/--
Unweighted finite marker-set specialization: if every deterministic object
makes total marker error at least one, then pointwise mixed error `ε` obeys
`1 ≤ |X| * ε`.
-/
theorem finiteMarkerPointwiseFloor
    (μ : C → ℝ) (err : C → X → ℝ) (ε : ℝ)
    (hμ : ∀ c, 0 ≤ μ c)
    (hμsum : ∑ c, μ c = 1)
    (hedge : ∀ c, 1 ≤ ∑ x, err c x)
    (hpoint : ∀ x, mixedError μ err x ≤ ε) :
    1 ≤ (Fintype.card X : ℝ) * ε := by
  have h := fractionalCorePointwiseFloor
      μ (fun _ : X => (1 : ℝ)) err ε
      hμ hμsum (fun _ => by norm_num)
      (fun c => by simpa using hedge c) hpoint
  simpa using h

/-- If `|X| * ε < 1`, a marker-hitting deterministic family has no such mixture. -/
theorem noPointwiseBelowFiniteMarkerScale
    (μ : C → ℝ) (err : C → X → ℝ) (ε : ℝ)
    (hμ : ∀ c, 0 ≤ μ c)
    (hμsum : ∑ c, μ c = 1)
    (hedge : ∀ c, 1 ≤ ∑ x, err c x)
    (hpoint : ∀ x, mixedError μ err x ≤ ε)
    (hsmall : (Fintype.card X : ℝ) * ε < 1) : False := by
  have hfloor := finiteMarkerPointwiseFloor μ err ε hμ hμsum hedge hpoint
  linarith

#print axioms mixedError
#print axioms weightedErrorFubini
#print axioms fractionalCoreAverageFloor
#print axioms fractionalCorePointwiseFloor
#print axioms noPointwiseBelowFractionalCore
#print axioms finiteMarkerPointwiseFloor
#print axioms noPointwiseBelowFiniteMarkerScale

end PNPPolynomialCoreFinite
end MillenniumBraid
