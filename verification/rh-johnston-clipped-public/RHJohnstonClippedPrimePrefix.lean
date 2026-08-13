import Mathlib

namespace RHJohnstonClippedPrimePrefix

noncomputable section

/-- On one prime gap, Johnston's unweighted Chebyshev deficit has the form
`energy + (x-theta)^2/2`, where `theta` and `energy` are frozen prime-prefix
data. -/
def gapDeficit (x theta energy : ℝ) : ℝ :=
  energy + (x - theta)^2 / 2

/-- Squared-distance penalty from `theta` to the closed interval `[l,u]`. -/
def clippedPenalty (l u theta : ℝ) : ℝ :=
  if theta ≤ l then (l - theta)^2 / 2
  else if u ≤ theta then (u - theta)^2 / 2
  else 0

/-- If the frozen Chebyshev prefix lies inside the gap, its value is the exact
gap minimum. -/
theorem interior_prefix_min
    {l u x theta energy : ℝ}
    (hxl : l ≤ x) (hxu : x ≤ u)
    (htl : l ≤ theta) (htu : theta ≤ u) :
    gapDeficit theta theta energy ≤ gapDeficit x theta energy := by
  unfold gapDeficit
  have hs : 0 ≤ (x - theta)^2 := sq_nonneg (x - theta)
  nlinarith

/-- If the frozen Chebyshev prefix is left of the gap, the left endpoint is the
exact minimum over the gap. -/
theorem left_clipped_min
    {l u x theta energy : ℝ}
    (hxl : l ≤ x) (hxu : x ≤ u)
    (ht : theta ≤ l) :
    gapDeficit l theta energy ≤ gapDeficit x theta energy := by
  unfold gapDeficit
  have hx : 0 ≤ x - l := sub_nonneg.mpr hxl
  have hl : 0 ≤ l - theta := sub_nonneg.mpr ht
  have hfactor : 0 ≤ (x - l) * (x + l - 2*theta) := by
    apply mul_nonneg hx
    nlinarith
  nlinarith [sq_nonneg (x-theta), sq_nonneg (l-theta)]

/-- If the frozen Chebyshev prefix is right of the gap, the right endpoint is
the exact minimum over the gap. -/
theorem right_clipped_min
    {l u x theta energy : ℝ}
    (hxl : l ≤ x) (hxu : x ≤ u)
    (ht : u ≤ theta) :
    gapDeficit u theta energy ≤ gapDeficit x theta energy := by
  unfold gapDeficit
  have hx : 0 ≤ u - x := sub_nonneg.mpr hxu
  have hu : 0 ≤ theta - u := sub_nonneg.mpr ht
  have hfactor : 0 ≤ (u - x) * (2*theta - u - x) := by
    apply mul_nonneg hx
    nlinarith
  nlinarith [sq_nonneg (x-theta), sq_nonneg (u-theta)]

/-- In the only genuinely dangerous case, when `theta` belongs to the gap,
strict positivity throughout the gap is equivalent to strict positivity of the
frozen prime-prefix energy. -/
theorem interior_gap_positive_iff_energy_positive
    {l u theta energy : ℝ}
    (htl : l ≤ theta) (htu : theta ≤ u) :
    (∀ x, l ≤ x → x ≤ u → 0 < gapDeficit x theta energy) ↔ 0 < energy := by
  constructor
  · intro hall
    have h := hall theta htl htu
    simpa [gapDeficit] using h
  · intro he x hxl hxu
    unfold gapDeficit
    have hs : 0 ≤ (x-theta)^2 / 2 := by positivity
    linarith

/-- Finite three-case clipped-minimum interface.  It makes no assertion that a
particular `l,u,theta,energy` comes from primes. -/
theorem clipped_minimum
    {l u x theta energy : ℝ}
    (hlu : l ≤ u) (hxl : l ≤ x) (hxu : x ≤ u) :
    (theta ≤ l → gapDeficit l theta energy ≤ gapDeficit x theta energy) ∧
    (l ≤ theta → theta ≤ u →
      gapDeficit theta theta energy ≤ gapDeficit x theta energy) ∧
    (u ≤ theta → gapDeficit u theta energy ≤ gapDeficit x theta energy) := by
  constructor
  · intro ht
    exact left_clipped_min hxl hxu ht
  constructor
  · intro htl htu
    exact interior_prefix_min hxl hxu htl htu
  · intro ht
    exact right_clipped_min hxl hxu ht

/-- Exact one-gap certificate: positivity at every point is equivalent to one
of three finite clipped tests.  In the interior case the test collapses to the
single frozen energy scalar. -/
theorem gap_positive_iff_clipped_certificate
    {l u theta energy : ℝ}
    (hlu : l ≤ u) :
    (∀ x, l ≤ x → x ≤ u → 0 < gapDeficit x theta energy) ↔
      ((theta ≤ l ∧ 0 < gapDeficit l theta energy) ∨
       (l ≤ theta ∧ theta ≤ u ∧ 0 < energy) ∨
       (u ≤ theta ∧ 0 < gapDeficit u theta energy)) := by
  constructor
  · intro hall
    rcases le_total theta l with htl | hlt
    · exact Or.inl ⟨htl, hall l le_rfl hlu⟩
    · rcases le_total theta u with htu | hut
      · have htheta := hall theta hlt htu
        have he : 0 < energy := by simpa [gapDeficit] using htheta
        exact Or.inr (Or.inl ⟨hlt, htu, he⟩)
      · exact Or.inr (Or.inr ⟨hut, hall u hlu le_rfl⟩)
  · intro hcert x hxl hxu
    rcases hcert with hleft | hrest
    · rcases hleft with ⟨ht, hpos⟩
      exact lt_of_lt_of_le hpos (left_clipped_min hxl hxu ht)
    · rcases hrest with hinterior | hright
      · rcases hinterior with ⟨htl, htu, he⟩
        exact (interior_gap_positive_iff_energy_positive htl htu).2 he x hxl hxu
      · rcases hright with ⟨ht, hpos⟩
        exact lt_of_lt_of_le hpos (right_clipped_min hxl hxu ht)

/-- Scalar seventh-object form of the one-gap criterion: the entire continuum
of points in `[l,u]` is positive iff one clipped scalar `energy + penalty` is
positive. -/
theorem gap_positive_iff_energy_plus_clipped_penalty
    {l u theta energy : ℝ}
    (hlu : l ≤ u) :
    (∀ x, l ≤ x → x ≤ u → 0 < gapDeficit x theta energy) ↔
      0 < energy + clippedPenalty l u theta := by
  by_cases hleft : theta ≤ l
  · simp [clippedPenalty, hleft]
    constructor
    · intro hall
      simpa [gapDeficit] using hall l le_rfl hlu
    · intro hpos x hxl hxu
      have hmin := left_clipped_min (energy := energy) hxl hxu hleft
      have hleftpos : 0 < gapDeficit l theta energy := by
        simpa [gapDeficit] using hpos
      exact lt_of_lt_of_le hleftpos hmin
  · have hlt : l < theta := lt_of_not_ge hleft
    by_cases hright : u ≤ theta
    · simp [clippedPenalty, hleft, hright]
      constructor
      · intro hall
        simpa [gapDeficit] using hall u hlu le_rfl
      · intro hpos x hxl hxu
        have hmin := right_clipped_min (energy := energy) hxl hxu hright
        have hrightpos : 0 < gapDeficit u theta energy := by
          simpa [gapDeficit] using hpos
        exact lt_of_lt_of_le hrightpos hmin
    · have htu : theta < u := lt_of_not_ge hright
      simp [clippedPenalty, hleft, hright]
      exact interior_gap_positive_iff_energy_positive (le_of_lt hlt) (le_of_lt htu)

#print axioms interior_prefix_min
#print axioms left_clipped_min
#print axioms right_clipped_min
#print axioms interior_gap_positive_iff_energy_positive
#print axioms clipped_minimum
#print axioms gap_positive_iff_clipped_certificate
#print axioms gap_positive_iff_energy_plus_clipped_penalty

end

end RHJohnstonClippedPrimePrefix
