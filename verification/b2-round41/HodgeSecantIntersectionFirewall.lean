import Mathlib

/-!
# Hodge relative-secant intersection firewall

This file formalizes only the elementary set-theoretic core: a set contained in
another set intersects it in itself, and therefore cannot simultaneously be
assigned positive codimension by a codimension function that assigns zero to
the whole set. It does not formalize projective spans, secant schemes,
degeneracy loci, Chow groups, Fourier--Mukai transforms, abelian varieties, or
the Hodge conjecture.
-/

namespace MillenniumBraid
namespace B2Round41Hodge

/-- A set contained in a candidate secant locus intersects that locus in
itself. -/
theorem self_intersection_of_subset
    {X : Type*} (Y S : Set X) (hYS : Y ⊆ S) :
    S ∩ Y = Y := by
  exact Set.inter_eq_right.mpr hYS

/-- Abstract codimension contradiction: if the whole set has codimension zero,
then its intersection with any containing set cannot have positive codimension.
-/
theorem containing_intersection_not_positive_codimension
    {X : Type*}
    (codim : Set X → ℕ) (Y S : Set X)
    (hYS : Y ⊆ S) (hwhole : codim Y = 0)
    {n : ℕ} (hn : 0 < n) :
    codim (S ∩ Y) ≠ n := by
  rw [self_intersection_of_subset Y S hYS, hwhole]
  omega

/-- Packaged contradiction with an asserted positive-codimension equality. -/
theorem positive_codimension_claim_false
    {X : Type*}
    (codim : Set X → ℕ) (Y S : Set X)
    (hYS : Y ⊆ S) (hwhole : codim Y = 0)
    {n : ℕ} (hn : 0 < n)
    (hclaim : codim (S ∩ Y) = n) : False := by
  exact (containing_intersection_not_positive_codimension
    codim Y S hYS hwhole hn) hclaim

#print axioms self_intersection_of_subset
#print axioms containing_intersection_not_positive_codimension
#print axioms positive_codimension_claim_false

end B2Round41Hodge
end MillenniumBraid
