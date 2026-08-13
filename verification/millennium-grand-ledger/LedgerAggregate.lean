import LedgerData
import RHCore
import SurplusCore
import UnitCore
import TriadCore
import SquareIdentity
import SeventhObjectAndInversion

namespace MillenniumGrandAggregate

open MillenniumGrandData
open MillenniumGrandExactObject

structure TargetPropositions where
  rh : Prop
  pnp : Prop
  bsd : Prop
  hodge : Prop
  navierStokes : Prop
  yangMills : Prop
  poincare : Prop
  seventhObjectInversion : Prop

def NoContradictorySides (T : TargetPropositions) : Prop :=
  ¬ (T.rh ∧ ¬ T.rh) ∧
  ¬ (T.pnp ∧ ¬ T.pnp) ∧
  ¬ (T.bsd ∧ ¬ T.bsd) ∧
  ¬ (T.hodge ∧ ¬ T.hodge) ∧
  ¬ (T.navierStokes ∧ ¬ T.navierStokes) ∧
  ¬ (T.yangMills ∧ ¬ T.yangMills) ∧
  ¬ (T.poincare ∧ ¬ T.poincare) ∧
  ¬ (T.seventhObjectInversion ∧ ¬ T.seventhObjectInversion)

theorem mutual_exclusivity_only
    (T : TargetPropositions) : NoContradictorySides T := by
  simp [NoContradictorySides]

structure CompiledLedger : Prop where
  rhCore : ∀ (a r : ℚ) (m n : ℕ),
    MillenniumGrandRH.forwardDiff (fun k => a * r ^ k) m n =
      a * r ^ n * (r - 1) ^ m
  pnpCore : ∀ (n c₁ c₂ o e₁ e₂ ell : ℤ),
    (c₁ + n - 2 * o + e₁ - ell) +
        (c₂ - (1 - o) + e₂ - 2 * (c₁ - n) + ell) = 2 * c₂ →
    (c₁ + c₂ - n) - (2 * n - 2) = (1 - o) + e₁ + e₂
  bsdCore : ∀ q : ℚ, 0 < q → q ^ 2 = 1 → q = 1
  hodgeCore : ∀ (x a : ℚ) (n : ℕ), n ≠ 0 →
    (n : ℚ) * x = a → x = a / (n : ℚ)
  navierStokesCore : ∀ (α β γ x y z : ℚ),
    α + β + γ = 0 →
    x * (α * y * z) + y * (β * z * x) + z * (γ * x * y) = 0
  yangMillsFiniteCore : ∀ A B : ℚ,
    A ^ 2 - B ^ 2 = (A - B) * (A + B)
  poincareFiniteCore : (4 : ℤ) - 6 + 4 - 1 = 1
  inversionFiniteCore : ∀ p : Bool × Bool,
    ((p.2, p.1).2, (p.2, p.1).1) = p
  exactObjectFirewall : ExactObjectFirewall
  exclusivityFirewall : ∀ T : TargetPropositions, NoContradictorySides T
  ledgerExact : TargetLedgerExact
  noAlarm : NoFiveAlarm
  bankNonempty : discoveryBank ≠ []

theorem compiled_ledger : CompiledLedger where
  rhCore := fun a r m n =>
    MillenniumGrandRH.geometric_forward_difference a r m n
  pnpCore := fun n c₁ c₂ o e₁ e₂ ell h =>
    MillenniumGrandSurplus.exact_surplus_identity n c₁ c₂ o e₁ e₂ ell h
  bsdCore := MillenniumGrandUnit.positive_square_unit_exactification
  hodgeCore := by
    intro x a n hn hmultiple
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    apply (eq_div_iff hnq).2
    simpa [mul_comm] using hmultiple
  navierStokesCore := fun α β γ x y z h =>
    GrandTriad.cancel α β γ x y z h
  yangMillsFiniteCore := GrandSquare.identity
  poincareFiniteCore := by norm_num
  inversionFiniteCore := by
    intro p
    rcases p with ⟨x, y⟩
    rfl
  exactObjectFirewall := exact_object_firewall
  exclusivityFirewall := mutual_exclusivity_only
  ledgerExact := target_ledger_exact
  noAlarm := no_five_alarm
  bankNonempty := by simp [discoveryBank]

#print axioms mutual_exclusivity_only
#print axioms compiled_ledger

end MillenniumGrandAggregate
