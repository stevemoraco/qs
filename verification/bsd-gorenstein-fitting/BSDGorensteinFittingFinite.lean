import Mathlib

/-!
# BSD Gorenstein/Fitting classification no-go: finite algebraic core

Honesty status: this file protects only scalar identities and a finite operator
countermodel used in the companion commutative-algebra note. It does not
formalize quotient polynomial rings, Gorenstein rings, Fitting ideals, module
duality, Selmer groups, Stark systems, or BSD.
-/

namespace MillenniumBraid
namespace BSDGorensteinFittingFinite

theorem fittingProductIdentity
    {R : Type*} [CommRing R]
    (x y : R) (hx : x * x = 0) (hy : y * y = 0) :
    (x + y) * (x + 2 * y) = 3 * (x * y) := by
  calc
    (x + y) * (x + 2 * y) = x * x + 3 * (x * y) + 2 * (y * y) := by ring
    _ = 3 * (x * y) := by rw [hx, hy]; ring

theorem recoverX
    {R : Type*} [CommRing R] (x y : R) :
    2 * (x + y) - (x + 2 * y) = x := by
  ring

theorem recoverY
    {R : Type*} [CommRing R] (x y : R) :
    (x + 2 * y) - (x + y) = y := by
  ring

abbrev F5 := ZMod 5
abbrev Vec4 := Fin 4 → F5

def xM (v : Vec4) : Vec4 := fun i =>
  if i = 3 then v 2 else 0

def xN (v : Vec4) : Vec4 := fun i =>
  if i = 1 then -v 0 else if i = 3 then -2 * v 2 else 0

abbrev KerM := {v : Vec4 // xM v = 0}
abbrev KerN := {v : Vec4 // xN v = 0}

theorem kerMCard : Fintype.card KerM = 125 := by
  native_decide

theorem kerNCard : Fintype.card KerN = 25 := by
  native_decide

theorem kernelCardEq_of_intertwining
    (f : Vec4 ≃ Vec4)
    (hzero : f 0 = 0)
    (hintertwine : ∀ v, f (xM v) = xN (f v)) :
    Fintype.card KerM = Fintype.card KerN := by
  let e : KerM ≃ KerN :=
    { toFun := fun v =>
        ⟨f v, by
          rw [← hintertwine v]
          rw [v.property, hzero]⟩
      invFun := fun w =>
        ⟨f.symm w, by
          apply f.injective
          rw [hintertwine]
          rw [f.apply_symm_apply, w.property, hzero]⟩
      left_inv := by
        intro v
        apply Subtype.ext
        exact f.symm_apply_apply v
      right_inv := by
        intro w
        apply Subtype.ext
        exact f.apply_symm_apply w }
  exact Fintype.card_congr e

theorem noZeroPreservingIntertwiningEquiv :
    ¬ ∃ f : Vec4 ≃ Vec4,
      f 0 = 0 ∧ ∀ v, f (xM v) = xN (f v) := by
  rintro ⟨f, hzero, hintertwine⟩
  have hcard := kernelCardEq_of_intertwining f hzero hintertwine
  rw [kerMCard, kerNCard] at hcard
  norm_num at hcard

#print axioms fittingProductIdentity
#print axioms recoverX
#print axioms recoverY
#print axioms kerMCard
#print axioms kerNCard
#print axioms kernelCardEq_of_intertwining
#print axioms noZeroPreservingIntertwiningEquiv

end BSDGorensteinFittingFinite
end MillenniumBraid
