import Mathlib

namespace MillenniumBraid
namespace BSDResidualSimilitude

theorem residualSimilitude_injective
    {K V W : Type*} [Field K]
    (B : V → V → K) (B' : W → W → K)
    (f : V → W) (u : K)
    (hu : u ≠ 0)
    (hsep : ∀ x y : V, (∀ z : V, B x z = B y z) → x = y)
    (hsim : ∀ x y : V, B' (f x) (f y) = u * B x y) :
    Function.Injective f := by
  intro x y hxy
  apply hsep x y
  intro z
  have hmul : u * B x z = u * B y z := by
    calc
      u * B x z = B' (f x) (f z) := (hsim x z).symm
      _ = B' (f y) (f z) := by rw [hxy]
      _ = u * B y z := hsim y z
  exact mul_left_cancel₀ hu hmul

theorem noNonzeroSimilitude_of_collision
    {K V W : Type*} [Field K]
    (B : V → V → K) (B' : W → W → K)
    (f : V → W)
    (hsep : ∀ x y : V, (∀ z : V, B x z = B y z) → x = y)
    (x y : V) (hxy : x ≠ y) (hcollision : f x = f y) :
    ¬ ∃ u : K, u ≠ 0 ∧ ∀ a b : V, B' (f a) (f b) = u * B a b := by
  rintro ⟨u, hu, hsim⟩
  have hinj := residualSimilitude_injective B B' f u hu hsep hsim
  exact hxy (hinj hcollision)

#print axioms residualSimilitude_injective
#print axioms noNonzeroSimilitude_of_collision

end BSDResidualSimilitude
end MillenniumBraid
