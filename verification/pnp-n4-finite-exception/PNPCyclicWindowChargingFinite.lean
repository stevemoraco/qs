import Mathlib

/-!
Finite charging cores for cyclic-window witness amplification.

HONESTY
* These theorems are finite counting implications only.
* They do not prove the circuit-semantic owner-locality hypothesis.
* They do not formalize Boolean circuits, Chen--Li--Yang magnification, or P vs NP.
* No `sorry`, `admit`, or project axiom occurs in this source.
-/

open scoped BigOperators

namespace Millennium
namespace PVsNP
namespace CyclicWindowCharging

/-- If every fiber of a charge map has cardinality at most `q`, then the
number of witnesses is at most `q` times the number of available units. -/
theorem card_le_mul_card_of_bounded_charge
    {Witness Unit : Type*}
    [Fintype Witness]
    [Fintype Unit]
    [DecidableEq Unit]
    (charge : Witness → Unit)
    (q : ℕ)
    (hfiber :
      ∀ u : Unit,
        ((Finset.univ : Finset Witness).filter
          (fun w => charge w = u)).card ≤ q) :
    Fintype.card Witness ≤ q * Fintype.card Unit := by
  classical
  have hcover :
      (Finset.univ : Finset Witness) =
        (Finset.univ : Finset Unit).biUnion
          (fun u =>
            (Finset.univ : Finset Witness).filter
              (fun w => charge w = u)) := by
    ext w
    simp
  calc
    Fintype.card Witness = (Finset.univ : Finset Witness).card := by simp
    _ = ((Finset.univ : Finset Unit).biUnion
          (fun u =>
            (Finset.univ : Finset Witness).filter
              (fun w => charge w = u))).card := by rw [hcover]
    _ ≤ ∑ u : Unit,
          ((Finset.univ : Finset Witness).filter
            (fun w => charge w = u)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _u : Unit, q := by
      exact Finset.sum_le_sum (fun u _hu => hfiber u)
    _ = q * Fintype.card Unit := by simp [Nat.mul_comm]

/-- Owner-local form. If each charged unit's owner is admissible for the
witness, and each owner is admissible for at most `q` witnesses, then the
charge congestion is automatically at most `q`. -/
theorem card_le_mul_card_of_owner_local_charge
    {Witness Unit Owner : Type*}
    [Fintype Witness]
    [Fintype Unit]
    [Fintype Owner]
    [DecidableEq Unit]
    [DecidableEq Owner]
    (charge : Witness → Unit)
    (owner : Unit → Owner)
    (Admissible : Witness → Owner → Prop)
    (q : ℕ)
    (hlocal : ∀ w : Witness, Admissible w (owner (charge w)))
    (howner :
      ∀ a : Owner,
        ((Finset.univ : Finset Witness).filter
          (fun w => Admissible w a)).card ≤ q) :
    Fintype.card Witness ≤ q * Fintype.card Unit := by
  classical
  apply card_le_mul_card_of_bounded_charge charge q
  intro u
  calc
    ((Finset.univ : Finset Witness).filter
        (fun w => charge w = u)).card
        ≤ ((Finset.univ : Finset Witness).filter
            (fun w => Admissible w (owner u))).card := by
          apply Finset.card_le_card
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          have h := hlocal w
          simpa [hw] using h
    _ ≤ q := howner (owner u)

/-- Multi-owner form. A charged unit may expose a bounded set of candidate
owners. If each unit has at most `a` candidates, every charged witness is
admissible for one candidate owner, and each owner is admissible for at most
`q` witnesses, then total congestion is at most `a*q`. -/
theorem card_le_mul_mul_card_of_multi_owner_charge
    {Witness Unit Owner : Type*}
    [Fintype Witness]
    [Fintype Unit]
    [Fintype Owner]
    [DecidableEq Unit]
    [DecidableEq Owner]
    (charge : Witness → Unit)
    (owners : Unit → Finset Owner)
    (Admissible : Witness → Owner → Prop)
    (a q : ℕ)
    (howners : ∀ u : Unit, (owners u).card ≤ a)
    (hlocal :
      ∀ w : Witness,
        ∃ owner ∈ owners (charge w), Admissible w owner)
    (howner :
      ∀ owner : Owner,
        ((Finset.univ : Finset Witness).filter
          (fun w => Admissible w owner)).card ≤ q) :
    Fintype.card Witness ≤ (a * q) * Fintype.card Unit := by
  classical
  apply card_le_mul_card_of_bounded_charge charge (a * q)
  intro u
  let fiber : Finset Witness :=
    (Finset.univ : Finset Witness).filter (fun w => charge w = u)
  let covered : Finset Witness :=
    (owners u).biUnion
      (fun owner =>
        (Finset.univ : Finset Witness).filter
          (fun w => Admissible w owner))
  have hsubset : fiber ⊆ covered := by
    intro w hw
    have hwEq : charge w = u := by
      simpa [fiber] using hw
    obtain ⟨owner, hownerMem, hadmissible⟩ := hlocal w
    have hownerMem' : owner ∈ owners u := by
      simpa [hwEq] using hownerMem
    simp only [covered, Finset.mem_biUnion]
    refine ⟨owner, hownerMem', ?_⟩
    simpa using hadmissible
  calc
    fiber.card ≤ covered.card := Finset.card_le_card hsubset
    _ ≤ ∑ owner ∈ owners u,
          ((Finset.univ : Finset Witness).filter
            (fun w => Admissible w owner)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _owner ∈ owners u, q := by
      gcongr with owner hownerMem
      exact howner owner
    _ = (owners u).card * q := by simp
    _ ≤ a * q := Nat.mul_le_mul_right q (howners u)

/-- Exceptional-witness form. If at most `r` witnesses are exempt from
charging and every remaining charge fiber has size at most `q`, then the total
witness count is at most `r + q*|Unit|`. -/
theorem card_le_exception_plus_mul_card
    {Witness Unit : Type*}
    [Fintype Witness]
    [Fintype Unit]
    [DecidableEq Witness]
    [DecidableEq Unit]
    (charge : Witness → Unit)
    (exceptional : Finset Witness)
    (r q : ℕ)
    (hexceptional : exceptional.card ≤ r)
    (hfiber :
      ∀ u : Unit,
        (((Finset.univ : Finset Witness) \ exceptional).filter
          (fun w => charge w = u)).card ≤ q) :
    Fintype.card Witness ≤ r + q * Fintype.card Unit := by
  classical
  have hcover :
      ((Finset.univ : Finset Witness) \ exceptional) =
        (Finset.univ : Finset Unit).biUnion
          (fun u =>
            (((Finset.univ : Finset Witness) \ exceptional).filter
              (fun w => charge w = u))) := by
    ext w
    simp
  have hremaining :
      ((Finset.univ : Finset Witness) \ exceptional).card ≤
        q * Fintype.card Unit := by
    calc
      ((Finset.univ : Finset Witness) \ exceptional).card =
          ((Finset.univ : Finset Unit).biUnion
            (fun u =>
              (((Finset.univ : Finset Witness) \ exceptional).filter
                (fun w => charge w = u)))).card :=
        congrArg Finset.card hcover
      _ ≤ ∑ u : Unit,
            (((Finset.univ : Finset Witness) \ exceptional).filter
              (fun w => charge w = u)).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ _u : Unit, q := by
        exact Finset.sum_le_sum (fun u _hu => hfiber u)
      _ = q * Fintype.card Unit := by simp [Nat.mul_comm]
  have hunion :
      (Finset.univ : Finset Witness) ⊆
        exceptional ∪ ((Finset.univ : Finset Witness) \ exceptional) := by
    intro w hw
    by_cases hwe : w ∈ exceptional
    · exact Finset.mem_union_left _ hwe
    · exact Finset.mem_union_right _ (by simp [hwe])
  calc
    Fintype.card Witness = (Finset.univ : Finset Witness).card := by simp
    _ ≤ (exceptional ∪
          ((Finset.univ : Finset Witness) \ exceptional)).card :=
      Finset.card_le_card hunion
    _ ≤ exceptional.card +
          ((Finset.univ : Finset Witness) \ exceptional).card :=
      Finset.card_union_le
    _ ≤ r + q * Fintype.card Unit :=
      Nat.add_le_add hexceptional hremaining

/-- Rational scalar endpoint: `n` witnesses charged with congestion `b`
force at least `n / b` units. -/
theorem rational_frontier_from_bounded_congestion
    (witnesses congestion units : ℚ)
    (hcongestion : 0 < congestion)
    (hcount : witnesses ≤ congestion * units) :
    witnesses / congestion ≤ units := by
  exact (div_le_iff₀ hcongestion).2 hcount

/-- If the exact circuit surplus equals the number of slack units, the finite
charge inequality transfers directly to a gate lower bound. -/
theorem gate_lower_from_exact_slack
    (g n witnesses congestion slack : ℚ)
    (hcongestion : 0 < congestion)
    (hcount : witnesses ≤ congestion * slack)
    (hexact : g - (2 * n - 2) = slack) :
    2 * n - 2 + witnesses / congestion ≤ g := by
  have hfrontier : witnesses / congestion ≤ slack :=
    rational_frontier_from_bounded_congestion
      witnesses congestion slack hcongestion hcount
  calc
    2 * n - 2 + witnesses / congestion ≤ 2 * n - 2 + slack := by
      linarith only [hfrontier]
    _ = g := by
      rw [← hexact]
      ring

#print axioms card_le_mul_card_of_bounded_charge
#print axioms card_le_mul_card_of_owner_local_charge
#print axioms card_le_mul_mul_card_of_multi_owner_charge
#print axioms card_le_exception_plus_mul_card
#print axioms rational_frontier_from_bounded_congestion
#print axioms gate_lower_from_exact_slack

end CyclicWindowCharging
end PVsNP
end Millennium
