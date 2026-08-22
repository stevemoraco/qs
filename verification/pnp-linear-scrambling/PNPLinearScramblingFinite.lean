import Mathlib

/-!
# P versus NP linear-scrambling finite firewalls

HONESTY BOUNDARY

This file verifies only finite logical and natural-number interfaces used in a
random linear-scrambling audit:

* a separator of a transported promise accepts the transported YES set and is
  contained in the transported high-side easy set;
* transported coordinate witnesses are accepted;
* a lower bound for a transformed problem transports back only after paying
  the inverse transformation cost;
* if every bad event in a uniform finite transformation family is nonempty,
  the sum of its atom probabilities cannot be below one once there are at
  least as many candidate circuits as transformations.

It does not formalize Boolean circuits, linear maps over F_2, random bases,
circuit counting, Gap-MCSP, the OPS magnification theorem, P, NP, or P/poly.
-/

namespace MillenniumBraid
namespace PNPLinearScramblingFinite

/-- Predicate form of the exact separator sandwich under a bijection. -/
theorem separator_sandwich
    {α : Type*}
    (transport : Equiv α α)
    (easySmall easyLarge accept : α → Prop)
    (_hsmallLarge : ∀ x, easySmall x → easyLarge x)
    (hyes : ∀ x, easySmall x → accept (transport x))
    (hno : ∀ x, ¬ easyLarge x → ¬ accept (transport x)) :
    (∀ x, easySmall x → accept (transport x)) ∧
      (∀ y, accept y → easyLarge (transport.symm y)) := by
  constructor
  · exact hyes
  · intro y hy
    by_contra hlarge
    have hreject : ¬ accept (transport (transport.symm y)) :=
      hno (transport.symm y) hlarge
    exact hreject (by simpa using hy)

/-- Every explicitly supplied low-side witness remains accepted after
transport. This is the finite logical core of the random-basis containment
argument. -/
theorem transported_witnesses_accepted
    {α ι : Type*}
    (transport : Equiv α α)
    (easySmall accept : α → Prop)
    (witness : ι → α)
    (hwitness : ∀ i, easySmall (witness i))
    (hyes : ∀ x, easySmall x → accept (transport x)) :
    ∀ i, accept (transport (witness i)) := by
  intro i
  exact hyes (witness i) (hwitness i)

/-- If computing the transformed problem can be done by first paying the
inverse-transform cost and then running a standard separator, the standard
size is bounded below only by the transformed lower bound minus that cost. -/
theorem paid_transport_lower_bound
    (standardSize transformCost transformedLower : ℕ)
    (htransport : transformedLower ≤ standardSize + transformCost) :
    transformedLower - transformCost ≤ standardSize := by
  omega

/-- Strict version: if every transformed separator has size above `Q`, then a
standard separator transported at cost `L` must have size above `Q-L`. -/
theorem paid_transport_strict
    (standardSize transformCost transformedSize Q : ℕ)
    (hcompose : transformedSize ≤ standardSize + transformCost)
    (hlower : Q < transformedSize) :
    Q - transformCost < standardSize ∨ Q < transformCost := by
  omega

/-- When the paid transformation cost already reaches the displayed lower
bound, subtraction yields no positive standard lower bound. -/
theorem overhead_can_consume_bound
    (Q transformCost : ℕ)
    (h : Q ≤ transformCost) :
    Q - transformCost = 0 := by
  omega

/-- Finite cardinality firewall behind the description-entropy warning.

If every circuit has a nonempty bad set of transformations and there are at
least as many circuits as transformations, then the sum of bad-set cardinalities
is at least the size of the transformation family. Dividing by the uniform
family size says the union-bound sum of atom probabilities is at least one. -/
theorem nonempty_bad_event_mass_floor
    {κ τ : Type*}
    [DecidableEq κ]
    [DecidableEq τ]
    (circuits : Finset κ)
    (transforms : Finset τ)
    (bad : κ → Finset τ)
    (hcount : transforms.card ≤ circuits.card)
    (hnonempty : ∀ c ∈ circuits, (bad c).Nonempty) :
    transforms.card ≤ ∑ c ∈ circuits, (bad c).card := by
  calc
    transforms.card ≤ circuits.card := hcount
    _ = ∑ _c ∈ circuits, 1 := by simp
    _ ≤ ∑ c ∈ circuits, (bad c).card := by
      apply Finset.sum_le_sum
      intro c hc
      exact Finset.one_le_card.mpr (hnonempty c hc)

/-- A zero-cost coordinate permutation is logically different from a paid
mixing transform. The theorem records only the arithmetic consequence of an
explicitly zero cost. -/
theorem zero_cost_transport
    (standardSize transformedLower : ℕ)
    (htransport : transformedLower ≤ standardSize + 0) :
    transformedLower ≤ standardSize := by
  simpa using htransport

#print axioms separator_sandwich
#print axioms transported_witnesses_accepted
#print axioms paid_transport_lower_bound
#print axioms paid_transport_strict
#print axioms overhead_can_consume_bound
#print axioms nonempty_bad_event_mass_floor
#print axioms zero_cost_transport

end PNPLinearScramblingFinite
end MillenniumBraid
