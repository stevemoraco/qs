import Mathlib

namespace MillenniumGrand

inductive Target where
  | riemannHypothesis | pVersusNP | birchSwinnertonDyer | hodgeConjecture
  | navierStokes | yangMills | poincareConjecture | objectInversion
  deriving DecidableEq, BEq, Repr

inductive ResearchStatus where
  | kernelVerifiedFiniteCore | openProblem | solvedBackground
  | researchObject | officialKernelVerified
  deriving DecidableEq, BEq, Repr

structure DiscoveryRecord where
  target : Target
  title : String
  status : ResearchStatus
  provenance : String
  deriving Repr

def discoveryBank : List DiscoveryRecord := [
  ⟨.riemannHypothesis, "finite difference core", .kernelVerifiedFiniteCore, "RH finite algebra"⟩,
  ⟨.pVersusNP, "surplus identity", .kernelVerifiedFiniteCore, "P-vs-NP finite algebra"⟩,
  ⟨.birchSwinnertonDyer, "square-unit exactification", .kernelVerifiedFiniteCore, "BSD finite algebra"⟩,
  ⟨.hodgeConjecture, "finite-multiple rationalization", .kernelVerifiedFiniteCore, "Hodge finite algebra"⟩,
  ⟨.navierStokes, "triad energy cancellation", .kernelVerifiedFiniteCore, "Navier-Stokes finite algebra"⟩,
  ⟨.yangMills, "power-difference telescoping", .kernelVerifiedFiniteCore, "Yang-Mills finite algebra"⟩,
  ⟨.poincareConjecture, "Poincare theorem", .solvedBackground, "Perelman background only"⟩,
  ⟨.objectInversion, "involutive route audit", .researchObject, "seventh-object firewall"⟩
]

def targetStatus : Target → ResearchStatus
  | .riemannHypothesis | .pVersusNP | .birchSwinnertonDyer
  | .hodgeConjecture | .navierStokes | .yangMills => .openProblem
  | .poincareConjecture => .solvedBackground
  | .objectInversion => .researchObject

def forwardDiff {R : Type*} [Sub R] (f : ℕ → R) : ℕ → ℕ → R
  | 0, n => f n
  | Nat.succ m, n => forwardDiff f m (n + 1) - forwardDiff f m n

theorem rh_geometric_forward_difference
    {R : Type*} [CommRing R] (a r : R) :
    ∀ m n : ℕ, forwardDiff (fun k => a * r ^ k) m n = a * r ^ n * (r - 1) ^ m := by
  intro m
  induction m with
  | zero => intro n; simp [forwardDiff]
  | succ m ih =>
      intro n
      simp only [forwardDiff, ih]
      rw [pow_succ r n, pow_succ (r - 1) m]
      ring

theorem pnp_exact_surplus_identity
    (n c₁ c₂ o endpointExcess outsideExcess ell : ℤ)
    (h : (c₁ + n - 2 * o + endpointExcess - ell) +
      (c₂ - (1 - o) + outsideExcess - 2 * (c₁ - n) + ell) = 2 * c₂) :
    (c₁ + c₂ - n) - (2 * n - 2) = (1 - o) + endpointExcess + outsideExcess := by
  linarith

theorem bsd_positive_square_unit_exactification
    (q : ℚ) (hpos : 0 < q) (hsquare : q ^ 2 = 1) : q = 1 := by
  have hfactor : (q - 1) * (q + 1) = 0 := by
    calc
      (q - 1) * (q + 1) = q ^ 2 - 1 := by ring
      _ = 0 := by rw [hsquare]; norm_num
  rcases mul_eq_zero.mp hfactor with hminus | hplus <;> linarith

theorem hodge_finite_multiple_rationalization
    (x a : ℚ) (n : ℕ) (hn : n ≠ 0) (hmultiple : (n : ℚ) * x = a) :
    x = a / (n : ℚ) := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  apply (eq_div_iff hnq).2
  simpa [mul_comm] using hmultiple

theorem navier_stokes_triad_energy_cancellation
    {R : Type*} [CommRing R] (α β γ x y z : R) (hcoeff : α + β + γ = 0) :
    x * (α * y * z) + y * (β * z * x) + z * (γ * x * y) = 0 := by
  calc
    x * (α * y * z) + y * (β * z * x) + z * (γ * x * y) =
        (α + β + γ) * (x * y * z) := by ring
    _ = 0 := by rw [hcoeff]; ring

def transferBridge {R : Type*} [Semiring R] (A B : R) : ℕ → R
  | 0 => 0
  | Nat.succ n => A ^ n + B * transferBridge A B n

theorem yang_mills_power_difference_telescoping
    {R : Type*} [CommRing R] (A B : R) :
    ∀ n : ℕ, A ^ n - B ^ n = (A - B) * transferBridge A B n := by
  intro n
  induction n with
  | zero => simp [transferBridge]
  | succ n ih =>
      simp only [transferBridge, pow_succ]
      calc
        A ^ n * A - B ^ n * B = (A - B) * A ^ n + B * (A ^ n - B ^ n) := by ring
        _ = (A - B) * A ^ n + B * ((A - B) * transferBridge A B n) := by rw [ih]
        _ = (A - B) * (A ^ n + B * transferBridge A B n) := by ring

theorem poincare_tetrahedron_euler : (4 : ℤ) - 6 + 4 - 1 = 1 := by norm_num

structure InversionObject (α : Type*) where
  invert : α → α
  involutive : Function.Involutive invert

def swapInversion (α : Type*) : InversionObject (α × α) where
  invert := fun p => (p.2, p.1)
  involutive := by intro p; rcases p with ⟨x, y⟩; rfl

theorem object_inversion_round_trip {α : Type*} (p : α × α) :
    (swapInversion α).invert ((swapInversion α).invert p) = p :=
  (swapInversion α).involutive p

structure TargetPropositions where
  rh : Prop
  pnp : Prop
  bsd : Prop
  hodge : Prop
  navierStokes : Prop
  yangMills : Prop
  poincare : Prop
  objectInversion : Prop

def NoContradictorySides (T : TargetPropositions) : Prop :=
  ¬ (T.rh ∧ ¬ T.rh) ∧ ¬ (T.pnp ∧ ¬ T.pnp) ∧ ¬ (T.bsd ∧ ¬ T.bsd) ∧
  ¬ (T.hodge ∧ ¬ T.hodge) ∧ ¬ (T.navierStokes ∧ ¬ T.navierStokes) ∧
  ¬ (T.yangMills ∧ ¬ T.yangMills) ∧ ¬ (T.poincare ∧ ¬ T.poincare) ∧
  ¬ (T.objectInversion ∧ ¬ T.objectInversion)

theorem mutual_exclusivity_does_not_choose_a_side (T : TargetPropositions) :
    NoContradictorySides T := by simp [NoContradictorySides]

theorem no_uniform_positive_side_chooser :
    ¬ (∀ P : Prop, (P ∨ ¬ P) → P) := by
  intro choosePositive
  exact choosePositive False (by simp)

structure BraidVerifiedCore : Prop where
  rhCore : ∀ (a r : ℤ) (m n : ℕ),
    forwardDiff (fun k => a * r ^ k) m n = a * r ^ n * (r - 1) ^ m
  pnpCore : ∀ (n c₁ c₂ o endpointExcess outsideExcess ell : ℤ),
    (c₁ + n - 2 * o + endpointExcess - ell) +
      (c₂ - (1 - o) + outsideExcess - 2 * (c₁ - n) + ell) = 2 * c₂ →
    (c₁ + c₂ - n) - (2 * n - 2) = (1 - o) + endpointExcess + outsideExcess
  bsdCore : ∀ q : ℚ, 0 < q → q ^ 2 = 1 → q = 1
  hodgeCore : ∀ (x a : ℚ) (n : ℕ), n ≠ 0 → (n : ℚ) * x = a → x = a / (n : ℚ)
  navierStokesCore : ∀ (α β γ x y z : ℤ), α + β + γ = 0 →
    x * (α * y * z) + y * (β * z * x) + z * (γ * x * y) = 0
  yangMillsCore : ∀ (A B : ℤ) (n : ℕ),
    A ^ n - B ^ n = (A - B) * transferBridge A B n
  poincareFiniteCore : (4 : ℤ) - 6 + 4 - 1 = 1
  objectInversionCore : ∀ p : ℕ × ℕ,
    (swapInversion ℕ).invert ((swapInversion ℕ).invert p) = p

theorem verifiedCore : BraidVerifiedCore where
  rhCore := rh_geometric_forward_difference
  pnpCore := pnp_exact_surplus_identity
  bsdCore := bsd_positive_square_unit_exactification
  hodgeCore := hodge_finite_multiple_rationalization
  navierStokesCore := navier_stokes_triad_energy_cancellation
  yangMillsCore := yang_mills_power_difference_telescoping
  poincareFiniteCore := poincare_tetrahedron_euler
  objectInversionCore := object_inversion_round_trip

def TargetLedgerExact : Prop :=
  targetStatus .riemannHypothesis = .openProblem ∧
  targetStatus .pVersusNP = .openProblem ∧
  targetStatus .birchSwinnertonDyer = .openProblem ∧
  targetStatus .hodgeConjecture = .openProblem ∧
  targetStatus .navierStokes = .openProblem ∧
  targetStatus .yangMills = .openProblem ∧
  targetStatus .poincareConjecture = .solvedBackground ∧
  targetStatus .objectInversion = .researchObject

theorem target_ledger_exact : TargetLedgerExact := by simp [TargetLedgerExact, targetStatus]

def NoSixAlarm : Prop := ∀ t : Target, targetStatus t ≠ .officialKernelVerified

theorem no_six_alarm : NoSixAlarm := by
  intro t
  cases t <;> simp [targetStatus]

structure GrandBraidStatement : Prop where
  verified : BraidVerifiedCore
  ledger : TargetLedgerExact
  noAlarm : NoSixAlarm
  mutualExclusivity : ∀ T : TargetPropositions, NoContradictorySides T
  noPositiveChooser : ¬ (∀ P : Prop, (P ∨ ¬ P) → P)
  bankNonempty : discoveryBank ≠ []

theorem millennium_grand_unified_executable : GrandBraidStatement where
  verified := verifiedCore
  ledger := target_ledger_exact
  noAlarm := no_six_alarm
  mutualExclusivity := mutual_exclusivity_does_not_choose_a_side
  noPositiveChooser := no_uniform_positive_side_chooser
  bankNonempty := by simp [discoveryBank]

#print axioms rh_geometric_forward_difference
#print axioms pnp_exact_surplus_identity
#print axioms bsd_positive_square_unit_exactification
#print axioms hodge_finite_multiple_rationalization
#print axioms navier_stokes_triad_energy_cancellation
#print axioms yang_mills_power_difference_telescoping
#print axioms object_inversion_round_trip
#print axioms no_uniform_positive_side_chooser
#print axioms millennium_grand_unified_executable

end MillenniumGrand
