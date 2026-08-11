import Mathlib

/-!
# Exact critical-path slack: finite wire-ledger algebra

Honesty status: this file formalizes only the affine integer accounting behind
one fan-in-two circuit wire count.  It does not formalize directed acyclic
graphs, Boolean gates, critical paths, probabilistic circuits, complexity
classes, Chen--Li--Yang, or `P != NP`.

The graph-theoretic proof that the ledger hypotheses hold is recorded in
`B4_PASS1_PNP_EXACT_CRITICAL_PATH_SLACK_2026-08-11.md`.
-/

namespace MillenniumBraid
namespace B4CriticalPathSlack

/--
Exact algebraic endpoint of the four-way wire ledger.

The intended meanings are:
* `c1,c2`: numbers of Type-1 and Type-2 nodes;
* `n,m,o`: inputs, outputs, and Type-1 outputs;
* `A,B`: exact outgoing-wire excesses;
* `l`: Type-1-to-Type-1 wires;
* `t12,t21,t22`: the other three directed wire counts;
* `g`: number of gates.

The hypotheses are equalities, not inequalities.  Eliminating the internal
wire counts yields the exact gate identity.
-/
theorem exactCriticalPathSlack
    (c1 c2 n m o A B l t12 t21 t22 g : ℤ)
    (h12 : t12 = c1 + n - 2 * o + A - l)
    (h21 : t21 = 2 * (c1 - n) - l)
    (h22 : t22 = c2 - (m - o) + B - t21)
    (hin : t12 + t22 = 2 * c2)
    (hg : g = c1 + c2 - n) :
    g = 2 * n - m - o + A + B := by
  linarith

/-- Exact surplus over the Feng--Li--Yang `2n-2m` baseline. -/
theorem exactSurplusAboveBaseline
    (n m o A B g : ℤ)
    (hformula : g = 2 * n - m - o + A + B) :
    g - (2 * n - 2 * m) = (m - o) + A + B := by
  linarith

/-- Single-output specialization: all positive surplus has three currencies. -/
theorem exactSingleOutputSurplus
    (n o A B g : ℤ)
    (hformula : g = 2 * n - 1 - o + A + B) :
    g - (2 * n - 2) = (1 - o) + A + B := by
  linarith

/-- The standard lower bound follows once all three surplus terms are nonnegative. -/
theorem baselineLowerBound
    (n m o A B g : ℤ)
    (hformula : g = 2 * n - m - o + A + B)
    (ho : o ≤ m)
    (hA : 0 ≤ A)
    (hB : 0 ≤ B) :
    2 * n - 2 * m ≤ g := by
  linarith

/-- Any claimed extra surplus must be paid by the exact recorded currencies. -/
theorem surplusForcesCurrency
    (n m o A B g S : ℤ)
    (hformula : g = 2 * n - m - o + A + B)
    (hsurplus : 2 * n - 2 * m + S ≤ g) :
    S ≤ (m - o) + A + B := by
  linarith

#print axioms exactCriticalPathSlack
#print axioms exactSurplusAboveBaseline
#print axioms exactSingleOutputSurplus
#print axioms baselineLowerBound
#print axioms surplusForcesCurrency

end B4CriticalPathSlack
end MillenniumBraid
