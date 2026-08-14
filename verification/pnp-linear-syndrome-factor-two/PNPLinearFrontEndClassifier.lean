import Mathlib

/-!
# Exact classifiers factoring through a linear sketch of two axes need 2n bits

Let

`A_n = (F₂^n × {0}) ∪ ({0} × F₂^n)`.

For positive `n`, suppose a classifier for membership in `A_n` factors as an
arbitrary decoder after a linear map

`H : F₂^n × F₂^n → F₂^r`.

Then `H` is injective.  Indeed, every nonzero kernel translation moves some
axis point off the union of axes, creating a yes/no collision at the decoder.
Consequently `r ≥ 2n`.

This strengthens the earlier syndrome theorem: injectivity on all axis
candidates need not be assumed. Exact classification through a linear
front-end already forces it globally.

The companion direct-classifier file shows that the same set has an
unrestricted `2n-1`-gate formula. Thus the theorem is an architecture boundary,
not an unrestricted circuit lower bound and not `P != NP`.
-/

namespace PNPLinearFrontEndClassifier

abbrev F2Vec (n : ℕ) := Fin n → ZMod 2

/-- The union of the two coordinate axes. -/
def IsAxis {n : ℕ} (x : F2Vec n × F2Vec n) : Prop :=
  x.1 = 0 ∨ x.2 = 0

/-- The first standard basis vector, available when `n>0`. -/
def firstBasis (n : ℕ) (hn : 0 < n) : F2Vec n :=
  fun j => if j = ⟨0, hn⟩ then 1 else 0

/-- The chosen basis vector is nonzero. -/
theorem firstBasis_ne_zero (n : ℕ) (hn : 0 < n) :
    firstBasis n hn ≠ 0 := by
  intro h
  have hcoord := congrFun h ⟨0, hn⟩
  simp [firstBasis] at hcoord

/-- Every nonzero translation moves at least one point of the axis union
outside the axis union. -/
theorem nonzero_translation_crosses_axis_boundary
    (n : ℕ)
    (hn : 0 < n)
    (z : F2Vec n × F2Vec n)
    (hz : z ≠ 0) :
    ∃ a,
      IsAxis a ∧
      ¬ IsAxis (a + z) := by
  let e : F2Vec n := firstBasis n hn
  have he : e ≠ 0 := firstBasis_ne_zero n hn
  rcases z with ⟨p, q⟩
  by_cases hp : p = 0
  · have hq : q ≠ 0 := by
      intro hq
      apply hz
      simp [hp, hq]
    refine ⟨(e, 0), ?_, ?_⟩
    · exact Or.inr rfl
    · simp [IsAxis, hp, hq, he]
  · by_cases hq : q = 0
    · refine ⟨(0, e), ?_, ?_⟩
      · exact Or.inl rfl
      · simp [IsAxis, hp, hq, he]
    · refine ⟨0, ?_, ?_⟩
      · exact Or.inl rfl
      · simp [IsAxis, hp, hq]

/-- Exact recognition of the axes through a linear front-end forces the
front-end to be injective, regardless of how powerful the decoder is. -/
theorem linear_front_end_injective
    (n r : ℕ)
    (hn : 0 < n)
    (H : (F2Vec n × F2Vec n) →ₗ[ZMod 2] F2Vec r)
    (decode : F2Vec r → Prop)
    (hcorrect : ∀ x, decode (H x) ↔ IsAxis x) :
    Function.Injective H := by
  intro x y hxy
  have hzker : H (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  by_contra hne
  obtain ⟨a, haAxis, haOff⟩ :=
    nonzero_translation_crosses_axis_boundary n hn (x - y) hne
  have hsame : H (a + (x - y)) = H a := by
    rw [map_add, hzker, add_zero]
  have hdecA : decode (H a) := (hcorrect a).2 haAxis
  have hdecShift : decode (H (a + (x - y))) := by
    simpa [hsame] using hdecA
  have haxisShift : IsAxis (a + (x - y)) :=
    (hcorrect (a + (x - y))).1 hdecShift
  exact haOff haxisShift

/-- Dimension consequence: an exact linear-front-end classifier for the axis
union exposes at least the full `2n` bits. -/
theorem linear_front_end_output_bits_lower
    (n r : ℕ)
    (hn : 0 < n)
    (H : (F2Vec n × F2Vec n) →ₗ[ZMod 2] F2Vec r)
    (decode : F2Vec r → Prop)
    (hcorrect : ∀ x, decode (H x) ↔ IsAxis x) :
    2 * n ≤ r := by
  have hinj : Function.Injective H :=
    linear_front_end_injective n r hn H decode hcorrect
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [F2Vec, two_mul] using hdim

#print axioms firstBasis_ne_zero
#print axioms nonzero_translation_crosses_axis_boundary
#print axioms linear_front_end_injective
#print axioms linear_front_end_output_bits_lower

end PNPLinearFrontEndClassifier
