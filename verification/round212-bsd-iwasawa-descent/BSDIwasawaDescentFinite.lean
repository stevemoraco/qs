import Mathlib

/-!
# Round 212 BSD Iwasawa-descent finite firewalls

This file formalizes only finite logical and arithmetic countermodels. It does
not formalize elliptic curves, Iwasawa algebras, Selmer groups, p-adic or
complex L-functions, Tate--Shafarevich groups, regulators, or BSD.
-/

namespace Millennium
namespace Round212BSD

/-- Scalar proxy for a cyclotomic Selmer corank decomposition. -/
def selmerCorankProxy (mordellWeil shaCorank : ℕ) : ℕ :=
  mordellWeil + shaCorank

/-- Vanishing of a `mu` proxy does not force a `lambda`/zero-order proxy to
vanish. -/
theorem mu_zero_does_not_force_lambda_zero :
    ¬ (∀ mu lambda : ℕ, mu = 0 → lambda = 0) := by
  intro h
  have hbad := h 0 1 rfl
  omega

/-- Even with `mu=0`, an arbitrary prescribed positive order proxy is possible. -/
theorem mu_zero_allows_arbitrary_order (r : ℕ) :
    ∃ mu lambda : ℕ, mu = 0 ∧ lambda = r := by
  exact ⟨0, r, rfl, rfl⟩

/-- Equality of the Selmer-corank proxy with analytic order does not identify
Mordell--Weil rank when a positive Sha-corank contribution remains. -/
theorem selmer_equality_does_not_force_rank_equality :
    ¬ (∀ analyticRank mordellWeil shaCorank : ℕ,
      selmerCorankProxy mordellWeil shaCorank = analyticRank →
      mordellWeil = analyticRank) := by
  intro h
  have hbad := h 1 0 1 (by norm_num [selmerCorankProxy])
  omega

/-- Exact scalar witness to the Selmer/Mordell--Weil distinction. -/
theorem positive_sha_corank_can_absorb_analytic_rank :
    selmerCorankProxy 0 1 = 1 ∧ (0 : ℕ) ≠ 1 := by
  norm_num [selmerCorankProxy]

/-- Linear central model. -/
def linearCentralModel (x : ℚ) : ℚ := x

/-- Quadratic central model. -/
def quadraticCentralModel (x : ℚ) : ℚ := x ^ 2

/-- Formal zero-order labels for the two models. -/
def linearOrderProxy : ℕ := 1

def quadraticOrderProxy : ℕ := 2

/-- Equal central values do not determine equal vanishing orders. -/
theorem central_value_interpolation_does_not_determine_order :
    linearCentralModel 0 = quadraticCentralModel 0 ∧
      linearOrderProxy ≠ quadraticOrderProxy := by
  norm_num [linearCentralModel, quadraticCentralModel,
    linearOrderProxy, quadraticOrderProxy]

/-- One primary component is finite while another is not. -/
def PrimaryFiniteProxy : Bool → Prop
  | false => True
  | true => False

/-- Existence of one finite primary component does not imply all-primary
finiteness. -/
theorem one_primary_component_finite_not_all :
    (∃ p, PrimaryFiniteProxy p) ∧
      ¬ (∀ p, PrimaryFiniteProxy p) := by
  constructor
  · exact ⟨false, trivial⟩
  · intro hall
    exact hall true

/-- Equal rank data do not imply finiteness of an independent obstruction
predicate. -/
theorem rank_equality_does_not_force_sha_finiteness :
    ¬ (∀ (analyticRank algebraicRank : ℕ) (FiniteSha : Prop),
      analyticRank = algebraicRank → FiniteSha) := by
  intro h
  exact h 0 0 False rfl

/-- A statement available only under a finiteness hypothesis cannot, as pure
logic, manufacture that hypothesis. -/
theorem conditional_formula_does_not_supply_finiteness :
    ¬ (∀ P : Prop, (P → True) → P) := by
  intro h
  exact h False (by intro hp; trivial)

/-- Deliberately named proxy for one local valuation test. -/
def onePrimeValuationProxy (ratio : ℚ) : ℤ :=
  if ratio = 2 then 0 else 1

/-- A zero result at one valuation proxy does not force the global ratio to be
one. -/
theorem one_prime_unit_information_not_scalar_equality :
    onePrimeValuationProxy 2 = 0 ∧ (2 : ℚ) ≠ 1 := by
  norm_num [onePrimeValuationProxy]

/-- A finite bad-reduction-prime proxy need not contain an unrelated arithmetic
prime that could support another primary obstruction. -/
theorem finite_bad_set_does_not_control_all_primary_indices :
    (2 : ℕ) ∈ ({2} : Finset ℕ) ∧
      (3 : ℕ) ∉ ({2} : Finset ℕ) := by
  norm_num

/-- Finite-prefix agreement does not force universal agreement. -/
def finiteTestModelA (_n : ℕ) : Bool := false

def finiteTestModelB (n : ℕ) : Bool := decide (n = 100)

theorem finite_database_agreement_does_not_close_universal_quantifier :
    (∀ n < 100, finiteTestModelA n = finiteTestModelB n) ∧
      finiteTestModelA 100 ≠ finiteTestModelB 100 := by
  constructor
  · intro n hn
    simp [finiteTestModelA, finiteTestModelB]
    omega
  · simp [finiteTestModelA, finiteTestModelB]

#print axioms mu_zero_does_not_force_lambda_zero
#print axioms mu_zero_allows_arbitrary_order
#print axioms selmer_equality_does_not_force_rank_equality
#print axioms positive_sha_corank_can_absorb_analytic_rank
#print axioms central_value_interpolation_does_not_determine_order
#print axioms one_primary_component_finite_not_all
#print axioms rank_equality_does_not_force_sha_finiteness
#print axioms conditional_formula_does_not_supply_finiteness
#print axioms one_prime_unit_information_not_scalar_equality
#print axioms finite_bad_set_does_not_control_all_primary_indices
#print axioms finite_database_agreement_does_not_close_universal_quantifier

end Round212BSD
end Millennium
