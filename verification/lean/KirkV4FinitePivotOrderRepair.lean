import Mathlib

namespace Millennium.YangMills

/-!
# Kirk v4 finite-pivot order repair

Finite scalar firewall/repair for the pivot-incidence step used around Kirk v4
Theorem 6.10, Lemma 6.12, and Lemma 6.30.

The printed multipivot estimate pays `exp (lambda * n(A))` by a support exponent
that is claimed linear in the pivot incidence `n(A)`.  For the downstream
landing theorem, however, only a finite selected pivot set of cardinality `N`
is ultimately required.  Once `N` is fixed first, `n(A) <= N` turns the entire
incidence charge into one finite prefactor.  A multipivot activity then needs
only one genuine `R`-scale support span; no diameter bound linear in `n(A)` is
needed for this fixed-`N` repair.

These theorems formalize only that finite arithmetic.  They do not prove the
source-level facts that selected incidence is bounded by the chosen finite
pivot count, that every multipivot reference factor has support span at least
`R`, or that the manuscript's parameter order can be rewritten while keeping
all other rows uniform.  No continuum, OS, spectral-gap, or Clay conclusion is
encoded here.
-/

/-- For nonnegative charge `lam`, incidence bounded by the fixed total pivot
count turns the pivot charge into a fixed finite prefactor. -/
theorem fixed_total_pivots_bound_charge
    (n N lam : ℝ)
    (hlam : 0 ≤ lam)
    (hnN : n ≤ N) :
    lam * n ≤ lam * N := by
  exact mul_le_mul_of_nonneg_left hnN hlam

/-- If a multipivot object has at least one genuine support span `R`, then after
fixing the total pivot count `N` first, a sufficiently large reserved support
payment `mu * R` absorbs the whole incidence charge `lam * n` plus any fixed
slack.  The proof uses only `n ≤ N`; no support diameter linear in `n` is
required. -/
theorem fixed_total_pivots_pay_charge_from_one_separation
    (n N R cost lam mu slack : ℝ)
    (hlam : 0 ≤ lam)
    (hmu : 0 ≤ mu)
    (hnN : n ≤ N)
    (hspan : R ≤ cost)
    (hbudget : lam * N + slack ≤ mu * R) :
    lam * n + slack ≤ mu * cost := by
  calc
    lam * n + slack ≤ lam * N + slack :=
      add_le_add_right (fixed_total_pivots_bound_charge n N lam hlam hnN) slack
    _ ≤ mu * R := hbudget
    _ ≤ mu * cost := mul_le_mul_of_nonneg_left hspan hmu

/-- Zero slack specialization: fixed finite incidence plus one separated support
span is enough to pay the complete incidence charge. -/
theorem fixed_total_pivots_pay_charge
    (n N R cost lam mu : ℝ)
    (hlam : 0 ≤ lam)
    (hmu : 0 ≤ mu)
    (hnN : n ≤ N)
    (hspan : R ≤ cost)
    (hbudget : lam * N ≤ mu * R) :
    lam * n ≤ mu * cost := by
  simpa using
    fixed_total_pivots_pay_charge_from_one_separation
      n N R cost lam mu 0 hlam hmu hnN hspan (by simpa using hbudget)

#check fixed_total_pivots_bound_charge
#check fixed_total_pivots_pay_charge_from_one_separation
#check fixed_total_pivots_pay_charge
#print axioms fixed_total_pivots_bound_charge
#print axioms fixed_total_pivots_pay_charge_from_one_separation
#print axioms fixed_total_pivots_pay_charge

end Millennium.YangMills
