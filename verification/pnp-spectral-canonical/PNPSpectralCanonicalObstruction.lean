import Mathlib

/-!
# P versus NP: canonical-representative obstruction cores

This file formalizes only the abstract finite logic and exponent arithmetic
behind a canonical-form obstruction isolated on 2026-08-11.

It does **not** formalize rational canonical form, similarity of matrices,
linear-circuit semantics, tensor rank, complexity classes, or `P != NP`.
-/

namespace PNP
namespace SpectralCanonicalObstruction

/--
If every invariant value has a representative whose cost is at most `cap`,
then no universal lower bound depending only on that invariant can exceed
`cap`.
-/
theorem invariant_lower_bound_capped_by_representative
    {X I : Type*}
    (inv : X → I)
    (cost : X → ℕ)
    (lower cap : I → ℕ)
    (rep : I → X)
    (hrepInv : ∀ i, inv (rep i) = i)
    (hrepCost : ∀ i, cost (rep i) ≤ cap i)
    (huniversal : ∀ x, lower (inv x) ≤ cost x) :
    ∀ i, lower i ≤ cap i := by
  intro i
  calc
    lower i = lower (inv (rep i)) := by rw [hrepInv i]
    _ ≤ cost (rep i) := huniversal (rep i)
    _ ≤ cap i := hrepCost i

/--
A property of the invariant cannot force cost strictly above the canonical
representative cap on every object in the corresponding invariant class.
-/
theorem invariant_property_cannot_force_above_cap
    {X I : Type*}
    (inv : X → I)
    (cost : X → ℕ)
    (cap : I → ℕ)
    (rep : I → X)
    (property : I → Prop)
    (hrepInv : ∀ i, inv (rep i) = i)
    (hrepCost : ∀ i, cost (rep i) ≤ cap i)
    (hforce : ∀ x, property (inv x) → cap (inv x) < cost x) :
    ∀ i, ¬ property i := by
  intro i hi
  have hproperty : property (inv (rep i)) := by
    simpa [hrepInv i] using hi
  have hstrict : cap (inv (rep i)) < cost (rep i) :=
    hforce (rep i) hproperty
  have hstrict' : cap i < cost (rep i) := by
    simpa [hrepInv i] using hstrict
  exact (not_lt_of_ge (hrepCost i)) hstrict'

/--
Constant linear-cap specialization.  In the matrix application the canonical
representative has `O(n)` nonzero entries, and hence `O(n)` linear-circuit cost.
-/
theorem invariant_lower_bound_le_constant_linear_cap
    {X I : Type*}
    (n c : ℕ)
    (inv : X → I)
    (cost : X → ℕ)
    (lower : I → ℕ)
    (rep : I → X)
    (hrepInv : ∀ i, inv (rep i) = i)
    (hrepCost : ∀ i, cost (rep i) ≤ c * n)
    (huniversal : ∀ x, lower (inv x) ≤ cost x) :
    ∀ i, lower i ≤ c * n := by
  exact invariant_lower_bound_capped_by_representative
    inv cost lower (fun _ => c * n) rep hrepInv hrepCost huniversal

/--
If a threshold is strictly larger than the cost of every canonical
representative, then no invariant class can satisfy a property asserted to
force that threshold for all of its representatives.
-/
theorem no_invariant_property_above_linear_cap
    {X I : Type*}
    (n c threshold : ℕ)
    (inv : X → I)
    (cost : X → ℕ)
    (rep : I → X)
    (property : I → Prop)
    (hrepInv : ∀ i, inv (rep i) = i)
    (hrepCost : ∀ i, cost (rep i) ≤ c * n)
    (hthreshold : c * n < threshold)
    (hforce : ∀ x, property (inv x) → threshold ≤ cost x) :
    ∀ i, ¬ property i := by
  intro i hi
  have hproperty : property (inv (rep i)) := by
    simpa [hrepInv i] using hi
  have hlower : threshold ≤ cost (rep i) := hforce (rep i) hproperty
  have hupper : cost (rep i) ≤ c * n := hrepCost i
  omega

/--
The exponent gap used by the elementary order-three tensor counting argument.
A rank-`r` decomposition has at most `3*r*n` scalar parameters, while an
`n × n × n` tensor has `n^3` coordinates.
-/
theorem trilinear_parameter_exponent_gap
    (n r : ℕ)
    (hn : 0 < n)
    (hr : 3 * r < n ^ 2) :
    3 * r * n < n ^ 3 := by
  have hmul := Nat.mul_lt_mul_of_pos_right hr hn
  simpa [pow_succ] using hmul

/--
A purely finite pigeonhole core: fewer descriptions than objects means some
object has no description.
-/
theorem description_space_too_small
    {Description Object : Type*}
    [Fintype Description] [Fintype Object]
    (decode : Description → Object)
    (hsmall : Fintype.card Description < Fintype.card Object) :
    ∃ obj, ∀ description, decode description ≠ obj := by
  by_contra h
  push_neg at h
  have hsurjective : Function.Surjective decode := by
    intro obj
    obtain ⟨description, hdecode⟩ := h obj
    exact ⟨description, hdecode⟩
  have hcard : Fintype.card Object ≤ Fintype.card Description :=
    Fintype.card_le_of_surjective decode hsurjective
  omega

#print axioms invariant_lower_bound_capped_by_representative
#print axioms invariant_property_cannot_force_above_cap
#print axioms invariant_lower_bound_le_constant_linear_cap
#print axioms no_invariant_property_above_linear_cap
#print axioms trilinear_parameter_exponent_gap
#print axioms description_space_too_small

end SpectralCanonicalObstruction
end PNP
