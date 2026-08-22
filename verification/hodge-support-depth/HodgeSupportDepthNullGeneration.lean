import Mathlib

/-!
# Hodge support-depth null-generation core

Finite additive induction only.  This file does not formalize complex tori,
coherent analytic sheaves, Fourier--Mukai transforms, Chern characters, Hodge
classes, algebraic cycles, or the Hodge conjecture.
-/

namespace MillenniumBraid
namespace HodgeSupportDepth

/--
If every class of support depth `n+1` is a sum of a class in the designated
null subgroup and a pushed class of depth `n`, if pushforward preserves the
null subgroups, and if depth zero is null, then every finite-depth class is
null.
-/
theorem all_mem_null_of_support_descent
    (G : ℕ → Type*)
    [∀ n, AddCommGroup (G n)]
    (null : ∀ n, AddSubgroup (G n))
    (push : ∀ n, G n →+ G (n + 1))
    (hpush : ∀ n (z : G n), z ∈ null n → push n z ∈ null (n + 1))
    (hbase : ∀ x : G 0, x ∈ null 0)
    (hstep : ∀ n (x : G (n + 1)),
      ∃ b : G (n + 1), ∃ z : G n,
        b ∈ null (n + 1) ∧ x = b + push n z) :
    ∀ n (x : G n), x ∈ null n := by
  intro n
  induction n with
  | zero =>
      intro x
      exact hbase x
  | succ n ih =>
      intro x
      obtain ⟨b, z, hb, hx⟩ := hstep n x
      rw [hx]
      exact (null (n + 1)).add_mem hb (hpush n z (ih z))

/--
Any additive transformation that vanishes on the null subgroup vanishes on all
finite-depth classes once the support-descent hypotheses hold.
-/
theorem transform_zero_of_support_descent
    (G : ℕ → Type*)
    [∀ n, AddCommGroup (G n)]
    (H : Type*)
    [AddCommGroup H]
    (null : ∀ n, AddSubgroup (G n))
    (push : ∀ n, G n →+ G (n + 1))
    (hpush : ∀ n (z : G n), z ∈ null n → push n z ∈ null (n + 1))
    (hbase : ∀ x : G 0, x ∈ null 0)
    (hstep : ∀ n (x : G (n + 1)),
      ∃ b : G (n + 1), ∃ z : G n,
        b ∈ null (n + 1) ∧ x = b + push n z)
    (tau : ∀ n, G n →+ H)
    (hnull : ∀ n (x : G n), x ∈ null n → tau n x = 0) :
    ∀ n (x : G n), tau n x = 0 := by
  intro n x
  exact hnull n x
    (all_mem_null_of_support_descent G null push hpush hbase hstep n x)

#print axioms all_mem_null_of_support_descent
#print axioms transform_zero_of_support_descent

end HodgeSupportDepth
end MillenniumBraid
