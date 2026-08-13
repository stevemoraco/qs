import Mathlib

open scoped BigOperators

/-!
# P versus NP: finite coded-marker transfer

This file formalizes a finite matrix/averaging lemma used by the P-vs-NP
research branch.

A single decoder `decode : Code -> X` is fixed independently of the
deterministic object.  If every deterministic object has an error at some
decoded code, then every mixture of deterministic objects has pointwise error
at least the reciprocal of the number of codes somewhere in the decoder image.
The decoder is not required to be injective.

This file deliberately does **not** define Boolean circuits, `B₂`, P, NP,
hardness magnification, asymptotics, or P versus NP.
-/

namespace MillenniumBraid
namespace PNPCodedMarkerFinite

variable {C X Code : Type*} [Fintype C] [Fintype Code]

/-- Mixed error at an ambient point. -/
def mixedError (mu : C -> ℝ) (err : C -> X -> ℝ) (x : X) : ℝ :=
  ∑ c, mu c * err c x

/-- Finite Fubini identity after decoding a finite code space into inputs. -/
theorem decodedErrorFubini
    (mu : C -> ℝ) (err : C -> X -> ℝ) (decode : Code -> X) :
    ∑ c, mu c * (∑ q, err c (decode q))
      = ∑ q, mixedError mu err (decode q) := by
  calc
    ∑ c, mu c * (∑ q, err c (decode q))
        = ∑ c, ∑ q, mu c * err c (decode q) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
    _ = ∑ q, ∑ c, mu c * err c (decode q) := by
          rw [Finset.sum_comm]
    _ = ∑ q, mixedError mu err (decode q) := by
          rfl

/--
A decoded witness for each deterministic object forces row error at least one.
Nonnegativity is the only property required of the error scores away from the
witness.
-/
theorem decodedWitnessImpliesRowFloor
    (err : C -> X -> ℝ) (decode : Code -> X)
    (herr0 : ∀ c x, 0 ≤ err c x)
    (hwitness : ∀ c, ∃ q, 1 ≤ err c (decode q)) :
    ∀ c, 1 ≤ ∑ q, err c (decode q) := by
  intro c
  obtain ⟨q, hq⟩ := hwitness c
  have hsingle : err c (decode q) ≤ ∑ q', err c (decode q') := by
    exact Finset.single_le_sum
      (fun q' _ => herr0 c (decode q'))
      (Finset.mem_univ q)
  exact hq.trans hsingle

/--
If each deterministic object has a decoded error witness, every normalized
nonnegative mixture has total mixed error at least one across the code space.
-/
theorem codedWitnessAverageFloor
    (mu : C -> ℝ) (err : C -> X -> ℝ) (decode : Code -> X)
    (hmu : ∀ c, 0 ≤ mu c)
    (hmusum : ∑ c, mu c = 1)
    (herr0 : ∀ c x, 0 ≤ err c x)
    (hwitness : ∀ c, ∃ q, 1 ≤ err c (decode q)) :
    1 ≤ ∑ q, mixedError mu err (decode q) := by
  have hrow := decodedWitnessImpliesRowFloor err decode herr0 hwitness
  calc
    1 = ∑ c, mu c := hmusum.symm
    _ ≤ ∑ c, mu c * (∑ q, err c (decode q)) := by
          apply Finset.sum_le_sum
          intro c _
          exact mul_le_mul_of_nonneg_left (hrow c) (hmu c)
    _ = ∑ q, mixedError mu err (decode q) :=
          decodedErrorFubini mu err decode

/--
If every ambient input has mixed error at most `epsilon`, a global code space
of cardinality `M` forces `1 ≤ M * epsilon`.

The decoder may have collisions: no injectivity hypothesis appears.
-/
theorem codedWitnessPointwiseFloor
    (mu : C -> ℝ) (err : C -> X -> ℝ) (decode : Code -> X) (epsilon : ℝ)
    (hmu : ∀ c, 0 ≤ mu c)
    (hmusum : ∑ c, mu c = 1)
    (herr0 : ∀ c x, 0 ≤ err c x)
    (hwitness : ∀ c, ∃ q, 1 ≤ err c (decode q))
    (hpoint : ∀ x, mixedError mu err x ≤ epsilon) :
    1 ≤ (Fintype.card Code : ℝ) * epsilon := by
  calc
    1 ≤ ∑ q, mixedError mu err (decode q) :=
      codedWitnessAverageFloor mu err decode hmu hmusum herr0 hwitness
    _ ≤ ∑ _q : Code, epsilon := by
      apply Finset.sum_le_sum
      intro q _
      exact hpoint (decode q)
    _ = (Fintype.card Code : ℝ) * epsilon := by
      simp

/-- A pointwise target below the reciprocal code scale is impossible. -/
theorem noPointwiseBelowCodedScale
    (mu : C -> ℝ) (err : C -> X -> ℝ) (decode : Code -> X) (epsilon : ℝ)
    (hmu : ∀ c, 0 ≤ mu c)
    (hmusum : ∑ c, mu c = 1)
    (herr0 : ∀ c x, 0 ≤ err c x)
    (hwitness : ∀ c, ∃ q, 1 ≤ err c (decode q))
    (hpoint : ∀ x, mixedError mu err x ≤ epsilon)
    (hsmall : (Fintype.card Code : ℝ) * epsilon < 1) : False := by
  have hfloor := codedWitnessPointwiseFloor
    mu err decode epsilon hmu hmusum herr0 hwitness hpoint
  linarith

/--
A useful bounded-description code shape: one of `b` templates together with an
ordered `r`-tuple of ambient indices from `[n]`.
-/
abbrev IndexCode (b r n : ℕ) := Fin b × (Fin r -> Fin n)

/-- Exact cardinality of the bounded-index code space. -/
theorem indexCode_card (b r n : ℕ) :
    Fintype.card (IndexCode b r n) = b * n ^ r := by
  simp [IndexCode]

#print axioms mixedError
#print axioms decodedErrorFubini
#print axioms decodedWitnessImpliesRowFloor
#print axioms codedWitnessAverageFloor
#print axioms codedWitnessPointwiseFloor
#print axioms noPointwiseBelowCodedScale
#print axioms indexCode_card

end PNPCodedMarkerFinite
end MillenniumBraid
