import Mathlib

/-!
# PNP constant-support image decoder: inverse-composition finite core

Honesty status: this file proves only that an ordered composition of
involutions is inverted by applying the same involutions in reverse order. It
does not formalize the Kaplan--Naor--Reingold permutation generator, the CLY
hash family, graph-syndrome decoding, circuit size, probabilistic circuits, NP,
or `P != NP`.
-/

namespace MillenniumBraid
namespace PNPInverseCompositionFinite

variable {α : Type*}

def applyForward : List (α → α) → α → α
  | [], x => x
  | f :: fs, x => applyForward fs (f x)

def applyBackward : List (α → α) → α → α
  | [], x => x
  | f :: fs, x => f (applyBackward fs x)

theorem backward_forward_cancel
    (fs : List (α → α))
    (hInv : ∀ f ∈ fs, Function.Involutive f) :
    ∀ x, applyBackward fs (applyForward fs x) = x := by
  induction fs with
  | nil =>
      intro x
      rfl
  | cons f fs ih =>
      intro x
      have hf : Function.Involutive f := hInv f (by simp)
      have hfs : ∀ g ∈ fs, Function.Involutive g := by
        intro g hg
        exact hInv g (by simp [hg])
      simp only [applyForward, applyBackward]
      rw [ih hfs (f x)]
      exact hf x

theorem forward_backward_cancel
    (fs : List (α → α))
    (hInv : ∀ f ∈ fs, Function.Involutive f) :
    ∀ x, applyForward fs (applyBackward fs x) = x := by
  induction fs with
  | nil =>
      intro x
      rfl
  | cons f fs ih =>
      intro x
      have hf : Function.Involutive f := hInv f (by simp)
      have hfs : ∀ g ∈ fs, Function.Involutive g := by
        intro g hg
        exact hInv g (by simp [hg])
      simp only [applyForward, applyBackward]
      rw [hf]
      exact ih hfs x

theorem forward_backward_bijection
    (fs : List (α → α))
    (hInv : ∀ f ∈ fs, Function.Involutive f) :
    Function.LeftInverse (applyBackward fs) (applyForward fs) ∧
      Function.RightInverse (applyBackward fs) (applyForward fs) := by
  constructor
  · exact backward_forward_cancel fs hInv
  · exact forward_backward_cancel fs hInv

#print axioms backward_forward_cancel
#print axioms forward_backward_cancel
#print axioms forward_backward_bijection

end PNPInverseCompositionFinite
end MillenniumBraid
