import Mathlib

/-!
# Round 216 P-versus-NP independence-seed finite cores

This file formalizes only finite support/cardinality implications, a coarse
log-budget inequality, and one exact finite parity-family countermodel. It does
not formalize probability distributions, Boolean circuits, marker languages,
pseudorandom generators, hardness magnification, P, NP, or P versus NP.
-/

namespace Millennium
namespace Round216PNP

abbrev Bits (k : ℕ) := Fin k → Bool

/-- A finite sample space whose projection onto `k` bits is surjective must
have at least `2^k` elements. Exact unbiased `k`-wise independence supplies
such a surjective projection on every chosen `k` coordinates. -/
theorem surjective_k_bit_projection_forces_support_size
    {Ω : Type*} [Fintype Ω]
    (k : ℕ)
    (project : Ω → Bits k)
    (hsurj : Function.Surjective project) :
    2 ^ k ≤ Fintype.card Ω := by
  have hcard : Fintype.card (Bits k) ≤ Fintype.card Ω :=
    Fintype.card_le_of_surjective project hsurj
  simpa [Bits] using hcard

/-- If `L` is a certified logarithmic description-count budget, a union-bound
requirement `L<k` and the coarse lower bound `g≤L` force more than `g`
independent coordinates. -/
theorem description_log_budget_forces_linear_independence
    (g L k : ℕ)
    (hlinear : g ≤ L)
    (hunion : L < k) :
    g < k := by
  omega

/-- The exact cardinality of a `k`-bit space. -/
theorem bit_space_card (k : ℕ) :
    Fintype.card (Bits k) = 2 ^ k := by
  simp [Bits]

/-- A two-bit parity family embedded in three output bits. -/
def parityExpand (s : Bits 2) : Bits 3 := fun i =>
  match i.1 with
  | 0 => s 0
  | 1 => s 1
  | _ => Bool.xor (s 0) (s 1)

/-- Projection to output coordinates zero and one. -/
def project01 (x : Bits 3) : Bits 2 := fun i =>
  match i.1 with
  | 0 => x 0
  | _ => x 1

/-- Projection to output coordinates zero and two. -/
def project02 (x : Bits 3) : Bits 2 := fun i =>
  match i.1 with
  | 0 => x 0
  | _ => x 2

/-- Projection to output coordinates one and two. -/
def project12 (x : Bits 3) : Bits 2 := fun i =>
  match i.1 with
  | 0 => x 1
  | _ => x 2

/-- Every pair of output coordinates of the parity family realizes all four
bit patterns, while the full three-bit map is not surjective. This is an exact
finite warning that all pairwise marginals can be perfect although point-mass
control remains only two-bit strength. -/
theorem parity_family_pairwise_surjective_but_not_global :
    Function.Surjective (project01 ∘ parityExpand) ∧
    Function.Surjective (project02 ∘ parityExpand) ∧
    Function.Surjective (project12 ∘ parityExpand) ∧
    ¬ Function.Surjective parityExpand := by
  native_decide

/-- The parity family has four seeds while the ambient selector space has
eight points. -/
theorem parity_family_seed_and_output_cards :
    Fintype.card (Bits 2) = 4 ∧
    Fintype.card (Bits 3) = 8 := by
  native_decide

#print axioms surjective_k_bit_projection_forces_support_size
#print axioms description_log_budget_forces_linear_independence
#print axioms bit_space_card
#print axioms parity_family_pairwise_surjective_but_not_global
#print axioms parity_family_seed_and_output_cards

end Round216PNP
end Millennium
