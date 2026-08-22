import Mathlib

namespace MillenniumGrandRH

def forwardDiff {R : Type*} [Sub R] (f : ℕ → R) : ℕ → ℕ → R
  | 0, n => f n
  | Nat.succ m, n => forwardDiff f m (n + 1) - forwardDiff f m n

theorem geometric_forward_difference
    {R : Type*} [CommRing R] (a r : R) :
    ∀ m n : ℕ,
      forwardDiff (fun k => a * r ^ k) m n =
        a * r ^ n * (r - 1) ^ m := by
  intro m
  induction m with
  | zero =>
      intro n
      simp [forwardDiff]
  | succ m ih =>
      intro n
      simp only [forwardDiff, ih]
      rw [pow_succ r n, pow_succ (r - 1) m]
      ring

#print axioms geometric_forward_difference

end MillenniumGrandRH
