import Mathlib

/-!
# Finite trace-commutator obstruction

Honesty status: this file formalizes only matrix-trace identities used in the
generic finite-length obstruction argument.

It does not formalize dual-number deformation algebras, finite-length modules,
localization, Poisson brackets, coherent sheaves, Hochschild cohomology, Ext,
semiregularity, Markman's construction, algebraic cycles, or the Hodge
Conjecture.
-/

namespace MillenniumBraid
namespace HodgeTraceCommutatorFinite

open Matrix

variable {R n : Type*}
variable [CommRing R]
variable [Fintype n]
variable [DecidableEq n]

/-- The trace of a finite matrix commutator is zero. -/
theorem trace_commutator_zero (F G : Matrix n n R) :
    trace (F * G - G * F) = 0 := by
  rw [trace_sub, trace_mul_comm]
  exact sub_self _

/-- A commutator cannot equal a scalar multiple of an endomorphism whose
scaled trace is nonzero. -/
theorem no_commutator_eq_smul_of_scaled_trace_ne
    (F G U : Matrix n n R)
    (e : R)
    (hcomm : F * G - G * F = e • U)
    (htrace : e • trace U ≠ 0) :
    False := by
  have h := congrArg trace hcomm
  rw [trace_commutator_zero, trace_smul] at h
  exact htrace h.symm

/-- If `U` is a scalar matrix plus a trace-zero correction, its trace is the
cardinality-weighted scalar. -/
theorem trace_scalar_one_add_of_trace_zero
    (c : R)
    (N : Matrix n n R)
    (hN : trace N = 0) :
    trace (c • (1 : Matrix n n R) + N) = c • (Fintype.card n : R) := by
  rw [trace_add, trace_smul, trace_one, hN, add_zero]

/-- Concrete contradiction interface: a commutator cannot equal `e` times a
scalar-plus-trace-zero matrix when the resulting cardinality-weighted scalar
has nonzero `e`-multiple. -/
theorem no_commutator_eq_scalar_plus_trace_zero
    (F G N : Matrix n n R)
    (e c : R)
    (hN : trace N = 0)
    (hcomm : F * G - G * F = e • (c • (1 : Matrix n n R) + N))
    (hnonzero : e • (c • (Fintype.card n : R)) ≠ 0) :
    False := by
  apply no_commutator_eq_smul_of_scaled_trace_ne F G
    (c • (1 : Matrix n n R) + N) e hcomm
  rw [trace_scalar_one_add_of_trace_zero c N hN]
  exact hnonzero

#print axioms trace_commutator_zero
#print axioms no_commutator_eq_smul_of_scaled_trace_ne
#print axioms trace_scalar_one_add_of_trace_zero
#print axioms no_commutator_eq_scalar_plus_trace_zero

end HodgeTraceCommutatorFinite
end MillenniumBraid
