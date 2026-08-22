import Mathlib

/-!
# BSD finite algebra: symmetry obstruction and jet weights

This file formalizes two reusable kernels behind
`JET_CAPACITY_AND_REPARAMETRIZATION_WEIGHT_OBSTRUCTION_2026-08-11.md`.
It does not prove BSD.

* An equivariant scalar output vanishes at an input fixed by an element whose
  target character is nontrivial.
* A list of homogeneous jet weights multiplies to the base raised to the sum
  of the weights.

The geometric input used in the accompanying note is that fewer than `r`
vector directions span a proper subspace of an `r`-dimensional space.  Its
pointwise stabilizer contains an element with nontrivial determinant
character, so the first theorem applies to a trivialized determinant line.
-/

namespace BSDProof
namespace JetCapacity

/-- If an input is fixed by a symmetry but a trivialized one-dimensional
    target is multiplied by a nontrivial character, every equivariant output
    at that input is zero.  No action laws or regularity of `phi` are needed. -/
theorem fixed_source_nontrivial_weight_zero
    {F G X : Type*} [Field F]
    (act : G → X → X)
    (weight : G → F)
    (phi : X → F)
    (equivariant : ∀ g x, phi (act g x) = weight g * phi x)
    {g : G} {x : X}
    (fixed : act g x = x)
    (nontrivial : weight g ≠ 1) :
    phi x = 0 := by
  have h : phi x = weight g * phi x := by
    calc
      phi x = phi (act g x) := by rw [fixed]
      _ = weight g * phi x := equivariant g x
  have hz : (1 - weight g) * phi x = 0 := by
    calc
      (1 - weight g) * phi x = phi x - weight g * phi x := by ring
      _ = 0 := sub_eq_zero.mpr h
  exact (mul_eq_zero.mp hz).resolve_left
    (sub_ne_zero.mpr (Ne.symm nontrivial))

/-- Multiplying homogeneous jet-coordinate weights `u^j` produces the total
    coordinate character `u` raised to the sum of the degrees. -/
theorem weighted_product_eq_pow_sum
    {M : Type*} [Monoid M] (u : M) :
    ∀ weights : List ℕ,
      (weights.map (fun j => u ^ j)).prod = u ^ weights.sum := by
  intro weights
  induction weights with
  | nil => simp
  | cons a tail ih => simp [ih, pow_add]

/-- The one-parameter jet of length `r` has weights `0,1,...,r-1`; this is the
    formal product identity before rewriting `List.sum (List.range r)` as
    `r*(r-1)/2`. -/
theorem one_parameter_jet_weight
    {M : Type*} [Monoid M] (u : M) (r : ℕ) :
    ((List.range r).map (fun j => u ^ j)).prod =
      u ^ (List.range r).sum := by
  exact weighted_product_eq_pow_sum u (List.range r)

end JetCapacity
end BSDProof
