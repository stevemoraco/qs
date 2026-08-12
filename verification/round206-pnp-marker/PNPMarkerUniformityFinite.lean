import Mathlib

/-!
# Round 206 P-versus-NP marker uniformity finite cores

This file formalizes only finite counting and arithmetic implications. It does
not formalize Boolean circuit semantics, critical paths, hardness magnification,
NP, P/poly, or P versus NP.
-/

namespace Millennium
namespace Round206PNP

/-- The exact Fan--Li--Yang wire ledger, with explicit excess-wire currencies,
implies the refined gate lower bound. -/
theorem critical_path_excess_slack
    (n m o c1 c2 g e1 e2 : ℕ)
    (hnodes : c1 + c2 = n + g)
    (houtputs : o ≤ m)
    (hwire : 3 * n + e1 + e2 ≤ c1 + c2 + m + o) :
    2 * n + (m - o) + e1 + e2 ≤ g + 2 * m := by
  omega

/-- For a single-output circuit, the surplus above `2n-2` must pay for the
output-location defect and both excess-wire ledgers. -/
theorem single_output_critical_path_excess_slack
    (n o c1 c2 g e1 e2 : ℕ)
    (hnodes : c1 + c2 = n + g)
    (houtputs : o ≤ 1)
    (hwire : 3 * n + e1 + e2 ≤ c1 + c2 + 1 + o) :
    2 * n + (1 - o) + e1 + e2 ≤ g + 2 := by
  exact critical_path_excess_slack
    n 1 o c1 c2 g e1 e2 hnodes houtputs hwire

/-- Three marker blocks of size `m` contain enough unordered marker pairs to
assign two distinct candidates to every one of the `m^2` cross pairs. This
subtraction-free inequality is exactly twice the required binomial capacity. -/
theorem marker_pair_capacity (m : ℕ) (hm : 1 ≤ m) :
    4 * (m * m) + 3 * m ≤ 9 * (m * m) := by
  have hmul : m ≤ m * m := by
    calc
      m = m * 1 := by simp
      _ ≤ m * m := Nat.mul_le_mul_left m hm
  omega

/-- A selector with one bit for each of `q` pair contexts has exactly `2^q`
possible assignments. -/
theorem selector_bits_card (q : ℕ) :
    Fintype.card (Fin q → Bool) = 2 ^ q := by
  simp

/-- A deliberately overcounted topological description type for `g` arbitrary
binary gates on `n` inputs, two constants, and one chosen output. -/
abbrev CircuitDescription (n g : ℕ) :=
  (Fin g → Fin 16 × Fin (n + g + 2) × Fin (n + g + 2)) ×
    Fin (n + g + 2)

/-- The overcounted circuit-description universe has the advertised cardinality. -/
theorem circuit_description_card (n g : ℕ) :
    Fintype.card (CircuitDescription n g) =
      (16 * ((n + g + 2) * (n + g + 2))) ^ g * (n + g + 2) := by
  simp [CircuitDescription]

/-- If the selector family is larger than the circuit-description universe,
no decoding map from descriptions can cover every selector. -/
theorem more_selectors_than_descriptions_not_surjective
    {Selector Description : Type*}
    [Fintype Selector] [Fintype Description]
    (decode : Description → Selector)
    (hcard : Fintype.card Description < Fintype.card Selector) :
    ¬ Function.Surjective decode := by
  intro hsurj
  have hle : Fintype.card Selector ≤ Fintype.card Description :=
    Fintype.card_le_of_surjective decode hsurj
  omega

/-- Applied to the explicit description overcount, a strict cardinality gap
produces a nonrepresented marker selector. -/
theorem marker_selector_counting_obstruction
    (n g q : ℕ)
    (decode : CircuitDescription n g → (Fin q → Bool))
    (hcard :
      (16 * ((n + g + 2) * (n + g + 2))) ^ g * (n + g + 2) < 2 ^ q) :
    ¬ Function.Surjective decode := by
  apply more_selectors_than_descriptions_not_surjective decode
  simpa [circuit_description_card, selector_bits_card] using hcard

/-- An existential hard selector at every length is only pointwise witness data;
it is not itself a uniformly computable selector function. -/
theorem pointwise_selector_witness_data
    {N S : Type*} (Good : N → S → Prop)
    (hpointwise : ∀ n, ∃ s, Good n s) :
    ∀ n, ∃ s, Good n s := by
  exact hpointwise

#print axioms critical_path_excess_slack
#print axioms single_output_critical_path_excess_slack
#print axioms marker_pair_capacity
#print axioms selector_bits_card
#print axioms circuit_description_card
#print axioms more_selectors_than_descriptions_not_surjective
#print axioms marker_selector_counting_obstruction
#print axioms pointwise_selector_witness_data

end Round206PNP
end Millennium
