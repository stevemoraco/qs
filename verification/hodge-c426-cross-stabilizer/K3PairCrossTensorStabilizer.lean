import Mathlib

/-!
# K3-pair cross-tensor stabilizer core

This file formalizes only the exact bilinear algebra used by the C426
projective-K3 pair-product source synthesis.

Let `A : V ≃ W` identify two underlying spaces, and suppose the pullback of the
bilinear form on `W` is represented on `V` by a self-adjoint-style operator
`S`:

`qW (A u) (A v) = qV (S u) v`.

If `g` preserves `qV`, then the conjugate `A g A⁻¹` preserves `qW` exactly when
`g` commutes with `S`, provided `g` is surjective and `qV` is left
nondegenerate. This is the finite algebra behind the graph-centralizer identity
in the product orthogonal group.

No K3 surface, Hodge structure, period map, Shimura variety, algebraic cycle,
or Hodge conjecture is encoded here.
-/

namespace Millennium.Hodge.K3PairCrossTensorStabilizer

variable {V W R : Type*}

/-- A map preserves a two-variable form. -/
def Preserves (q : V → V → R) (g : V → V) : Prop :=
  ∀ u v, q (g u) (g v) = q u v

/-- Left nondegeneracy in the only form needed by the converse theorem. -/
def LeftNondegenerate (q : V → V → R) : Prop :=
  ∀ x y, (∀ z, q x z = q y z) → x = y

/--
If `g` preserves `qV` and commutes with the pullback operator `S`, then the
cross-conjugate action preserves `qW` in source coordinates.
-/
theorem cross_preserves_of_commute
    (A : V ≃ W)
    (qV : V → V → R) (qW : W → W → R)
    (S g : V → V)
    (hpull : ∀ u v, qW (A u) (A v) = qV (S u) v)
    (hg : Preserves qV g)
    (hcomm : Function.Commute S g) :
    ∀ u v, qW (A (g u)) (A (g v)) = qW (A u) (A v) := by
  intro u v
  calc
    qW (A (g u)) (A (g v)) = qV (S (g u)) (g v) := hpull (g u) (g v)
    _ = qV (g (S u)) (g v) := by rw [hcomm u]
    _ = qV (S u) v := hg (S u) v
    _ = qW (A u) (A v) := (hpull u v).symm

/--
The same preservation statement written literally for the conjugate map on
`W`.
-/
theorem conjugate_preserves_of_commute
    (A : V ≃ W)
    (qV : V → V → R) (qW : W → W → R)
    (S g : V → V)
    (hpull : ∀ u v, qW (A u) (A v) = qV (S u) v)
    (hg : Preserves qV g)
    (hcomm : Function.Commute S g) :
    Preserves qW (fun w => A (g (A.symm w))) := by
  intro x y
  simpa using
    cross_preserves_of_commute A qV qW S g hpull hg hcomm (A.symm x) (A.symm y)

/--
Conversely, if the cross-conjugate action preserves `qW`, then `g` commutes
with `S`. Surjectivity of `g` lets the test vector range over all of `V`, and
left nondegeneracy identifies the two first arguments.
-/
theorem commute_of_cross_preserves
    (A : V ≃ W)
    (qV : V → V → R) (qW : W → W → R)
    (S g : V → V)
    (hpull : ∀ u v, qW (A u) (A v) = qV (S u) v)
    (hg : Preserves qV g)
    (hsurj : Function.Surjective g)
    (hnd : LeftNondegenerate qV)
    (hcross : ∀ u v, qW (A (g u)) (A (g v)) = qW (A u) (A v)) :
    Function.Commute S g := by
  intro u
  apply hnd (S (g u)) (g (S u))
  intro z
  obtain ⟨v, rfl⟩ := hsurj z
  calc
    qV (S (g u)) (g v) = qW (A (g u)) (A (g v)) :=
      (hpull (g u) (g v)).symm
    _ = qW (A u) (A v) := hcross u v
    _ = qV (S u) v := hpull u v
    _ = qV (g (S u)) (g v) := (hg (S u) v).symm

/--
Exact graph-stabilizer equivalence in source coordinates.
-/
theorem cross_preservation_iff_commute
    (A : V ≃ W)
    (qV : V → V → R) (qW : W → W → R)
    (S g : V → V)
    (hpull : ∀ u v, qW (A u) (A v) = qV (S u) v)
    (hg : Preserves qV g)
    (hsurj : Function.Surjective g)
    (hnd : LeftNondegenerate qV) :
    (∀ u v, qW (A (g u)) (A (g v)) = qW (A u) (A v)) ↔
      Function.Commute S g := by
  constructor
  · intro hcross
    exact commute_of_cross_preserves A qV qW S g hpull hg hsurj hnd hcross
  · intro hcomm
    exact cross_preserves_of_commute A qV qW S g hpull hg hcomm

/--
Literal conjugate-map version of the graph-stabilizer equivalence.
-/
theorem conjugate_preservation_iff_commute
    (A : V ≃ W)
    (qV : V → V → R) (qW : W → W → R)
    (S g : V → V)
    (hpull : ∀ u v, qW (A u) (A v) = qV (S u) v)
    (hg : Preserves qV g)
    (hsurj : Function.Surjective g)
    (hnd : LeftNondegenerate qV) :
    Preserves qW (fun w => A (g (A.symm w))) ↔ Function.Commute S g := by
  constructor
  · intro hconj
    apply commute_of_cross_preserves A qV qW S g hpull hg hsurj hnd
    intro u v
    simpa using hconj (A u) (A v)
  · intro hcomm
    exact conjugate_preserves_of_commute A qV qW S g hpull hg hcomm

#print axioms cross_preserves_of_commute
#print axioms conjugate_preserves_of_commute
#print axioms commute_of_cross_preserves
#print axioms cross_preservation_iff_commute
#print axioms conjugate_preservation_iff_commute

end Millennium.Hodge.K3PairCrossTensorStabilizer
