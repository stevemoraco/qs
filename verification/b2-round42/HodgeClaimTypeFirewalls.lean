import Mathlib

/-!
# Current claimed-Hodge-proof finite type firewalls

This file formalizes only integer degree and divisibility shadows used in the
round-42 Hodge audit. It does not formalize varieties, Chow groups,
correspondences, motives, Tate twists, cohomology, Picard groups, or Hodge.
-/

namespace MillenniumBraid
namespace B2Round42Hodge

/-- A positive correspondence degree cannot equal the negative degree required
by inverse Lefschetz unless the degree is zero. -/
theorem positive_degree_not_negative
    {r : ℤ} (hr : 0 < r) :
    r ≠ -r := by
  intro h
  linarith

/-- The codimensions `n+r` and `n-r` differ for every positive `r`. -/
theorem transpose_codimension_not_inverse_codimension
    {n r : ℤ} (hr : 0 < r) :
    n + r ≠ n - r := by
  intro h
  linarith

/-- Smallest surface instance: codimension three is not codimension one. -/
theorem surface_transpose_wrong_codimension :
    (2 : ℤ) + 1 ≠ 2 - 1 := by
  norm_num

/-- The integer Picard generator has no additive half. -/
theorem integer_one_not_two_divisible :
    ¬ ∃ m : ℤ, 2 * m = 1 := by
  intro h
  obtain ⟨m, hm⟩ := h
  omega

/-- Therefore the additive group of integers is not divisible by two. -/
theorem integers_not_two_divisible :
    ¬ ∀ z : ℤ, ∃ w : ℤ, 2 * w = z := by
  intro hall
  exact integer_one_not_two_divisible (hall 1)

/-- Abstract firewall: a group in which every element has a half cannot be
identified with integers by a bijection preserving doubling. -/
theorem divisible_source_not_isomorphic_to_integers
    {V : Type*}
    (double : V → V)
    (f : V → ℤ)
    (hsurj : Function.Surjective f)
    (hhalf : ∀ v : V, ∃ w : V, double w = v)
    (hpres : ∀ w : V, f (double w) = 2 * f w) :
    False := by
  obtain ⟨v, hv⟩ := hsurj 1
  obtain ⟨w, hw⟩ := hhalf v
  have hcalc : 2 * f w = 1 := by
    calc
      2 * f w = f (double w) := (hpres w).symm
      _ = f v := by rw [hw]
      _ = 1 := hv
  exact integer_one_not_two_divisible ⟨f w, hcalc⟩

#print axioms positive_degree_not_negative
#print axioms transpose_codimension_not_inverse_codimension
#print axioms surface_transpose_wrong_codimension
#print axioms integer_one_not_two_divisible
#print axioms integers_not_two_divisible
#print axioms divisible_source_not_isomorphic_to_integers

end B2Round42Hodge
end MillenniumBraid
