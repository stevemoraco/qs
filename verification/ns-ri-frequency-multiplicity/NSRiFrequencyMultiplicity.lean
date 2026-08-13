import Mathlib

/-!
# Finite frequency-label multiplicity firewall for arXiv:2601.15685v1

This file verifies only the finite combinatorial core of the audit of equation
(3.12): many cutoff indices may map to one exceptional shell label, so summing
the repeated shell weight is not bounded by the number of distinct labels times
the maximum shell weight. It does not formalize logarithms, Fourier analysis,
the Navier--Stokes equations, or any global regularity theorem.
-/

namespace MillenniumBraid
namespace NSRiFrequencyMultiplicity

/-- A finite family of cutoff indices all mapped to one shell label. -/
def repeatedShell {N : Nat} (_k : Fin N) : Fin 1 := 0

/-- The first decisive source ratio, corresponding to `m = 4`, has the lower
shell weight `b(J_m) ≥ 2^(m-1) = 8`. -/
def exceptionalWeight (_j : Fin 1) : Nat := 8

/-- Reusing one label `N` times counts its weight `N` times. -/
theorem repeated_shell_sum (N : Nat) :
    (∑ k : Fin N, exceptionalWeight (repeatedShell k)) = N * 8 := by
  simp [exceptionalWeight]

/-- Counting one distinct label instead of its four preimages undercounts the
weighted sum by a factor four. -/
theorem distinct_label_max_bound_fails :
    ¬ ((∑ k : Fin 4, exceptionalWeight (repeatedShell k)) ≤
        Fintype.card (Fin 1) * 8) := by
  norm_num [exceptionalWeight, repeatedShell]

/-- At the `m = 4` source ratio, if `n = 2N` and one exceptional shell has `N`
preimages of weight at least eight, then its contribution alone exceeds the
claimed `3n` budget for every positive `N`. -/
theorem ri_m4_three_n_bound_fails (N : Nat) (hN : 0 < N) :
    3 * (2 * N) <
      ∑ k : Fin N, exceptionalWeight (repeatedShell k) := by
  rw [repeated_shell_sum]
  omega

#print axioms repeated_shell_sum
#print axioms distinct_label_max_bound_fails
#print axioms ri_m4_three_n_bound_fails

end NSRiFrequencyMultiplicity
end MillenniumBraid
