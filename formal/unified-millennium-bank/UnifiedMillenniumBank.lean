import Mathlib

/-!
# Unified executable Millennium research bank

This is a single standalone Lean file collecting representative finite theorem
cores for RH, P versus NP, BSD, Hodge, Navier--Stokes, Yang--Mills, the
cross-problem closed-limit mechanism, and the cycle-safe retraction (the
"seventh object" inversion pattern).

It deliberately does not define the official Clay statements.  The finite
firewalls below are unconditional, but none is silently promoted to a proof of
an official Millennium theorem.
-/

open Filter Finset

namespace Millennium.Unified

/-! ## RH: positive-part Bregman spine -/

namespace RH

def positivePart (x : ℝ) : ℝ := max x 0

def positiveEnergy (x : ℝ) : ℝ := positivePart x ^ 2 / 2

def bregmanResidual (a b : ℝ) : ℝ :=
  positivePart b * (b - a) - (positiveEnergy b - positiveEnergy a)

theorem positiveEnergy_nonneg (x : ℝ) : 0 ≤ positiveEnergy x := by
  unfold positiveEnergy
  positivity

theorem bregmanResidual_nonneg (a b : ℝ) : 0 ≤ bregmanResidual a b := by
  unfold bregmanResidual positiveEnergy positivePart
  by_cases hb : 0 ≤ b
  · rw [max_eq_left hb]
    by_cases ha : 0 ≤ a
    · rw [max_eq_left ha]
      nlinarith [sq_nonneg (b - a)]
    · have ha' : a ≤ 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      have hab : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha' hb
      nlinarith
  · have hb' : b ≤ 0 := le_of_not_ge hb
    rw [max_eq_right hb']
    by_cases ha : 0 ≤ a
    · rw [max_eq_left ha]
      positivity
    · have ha' : a ≤ 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      norm_num

theorem bregman_step_identity (a b : ℝ) :
    positivePart b * (b - a) =
      positiveEnergy b - positiveEnergy a + bregmanResidual a b := by
  unfold bregmanResidual
  ring

theorem positiveEnergy_mono {a b : ℝ} (hab : a ≤ b) :
    positiveEnergy a ≤ positiveEnergy b := by
  unfold positiveEnergy positivePart
  by_cases hb : 0 ≤ b
  · rw [max_eq_left hb]
    by_cases ha : 0 ≤ a
    · rw [max_eq_left ha]
      have hsum : 0 ≤ a + b := add_nonneg ha hb
      have hdiff : 0 ≤ b - a := sub_nonneg.mpr hab
      nlinarith [mul_nonneg hdiff hsum]
    · have ha' : a ≤ 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      positivity
  · have hb' : b ≤ 0 := le_of_not_ge hb
    have ha' : a ≤ 0 := hab.trans hb'
    rw [max_eq_right ha', max_eq_right hb']

theorem weighted_energy_abel (energy weight : ℕ → ℝ) (n : ℕ) :
    (∑ i in range (n + 1), weight i * (energy (i + 1) - energy i)) =
      weight n * energy (n + 1) - weight 0 * energy 0 +
        ∑ i in range n, (weight i - weight (i + 1)) * energy (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ, sum_range_succ, ih]
      ring

end RH

/-! ## P versus NP: local choices do not erase global constraints -/

namespace PNP

abbrev ChoiceWalk (n : ℕ) := Fin n → Bool
abbrev LayerNode (n : ℕ) := Fin (n + 1) × Bool

theorem layerNode_card (n : ℕ) :
    Fintype.card (LayerNode n) = (n + 1) * 2 := by
  simp [LayerNode]

theorem choiceWalk_card (n : ℕ) :
    Fintype.card (ChoiceWalk n) = 2 ^ n := by
  simp [ChoiceWalk]

def correlated2 (w : ChoiceWalk 2) : Prop := w 0 = w 1

theorem every_local_value_extends (i : Fin 2) (b : Bool) :
    ∃ w : ChoiceWalk 2, correlated2 w ∧ w i = b := by
  refine ⟨fun _ => b, ?_, rfl⟩
  rfl

def mixed2 : ChoiceWalk 2 := fun i => if i = 0 then false else true

theorem mixed2_not_correlated : ¬ correlated2 mixed2 := by
  simp [correlated2, mixed2]

theorem all_local_extensions_do_not_force_global :
    (∀ i : Fin 2, ∃ w : ChoiceWalk 2, correlated2 w ∧ w i = mixed2 i) ∧
      ¬ correlated2 mixed2 := by
  constructor
  · intro i
    exact every_local_value_extends i (mixed2 i)
  · exact mixed2_not_correlated

theorem constrained_walk_exists_exact {n : ℕ} (P : ChoiceWalk n → Prop) :
    (∃ w : ChoiceWalk n, P w) ↔ ∃ a : Fin n → Bool, P a := by
  rfl

end PNP

/-! ## BSD: object dimension and eigenspace typing firewalls -/

namespace BSD

def fiberPowerDim (baseDim fiberDim r : ℕ) : ℕ := baseDim + r * fiberDim

theorem universalEllipticFiberPower_dim (r : ℕ) :
    fiberPowerDim 1 1 r = r + 1 := by
  simp [fiberPowerDim, Nat.add_comm]

theorem universalFiberPower_not_two_r {r : ℕ} (hr : 2 ≤ r) :
    fiberPowerDim 1 1 r ≠ 2 * r := by
  rw [universalEllipticFiberPower_dim]
  omega

theorem doubleFiberProduct_dimension_gap :
    fiberPowerDim 1 1 2 = 3 ∧ fiberPowerDim 1 1 2 ≠ 4 := by
  norm_num [fiberPowerDim]

def fixedCurveDiagonalCodim (r : ℕ) : ℕ := r - 1

theorem diagonalCodim_not_r {r : ℕ} (hr : 0 < r) :
    fixedCurveDiagonalCodim r ≠ r := by
  simp [fixedCurveDiagonalCodim]
  omega

def signInvolution (x : ℝ) : ℝ := -x

theorem minus_one_eigenspace_does_not_force_zero :
    ∃ x : ℝ, x ≠ 0 ∧ signInvolution x = -x := by
  exact ⟨1, by norm_num [signInvolution]⟩

end BSD

/-! ## Hodge: secant containment and one-section embedding firewalls -/

namespace Hodge

theorem intersection_eq_of_contained
    {α : Type*} {Y Σ : Set α} (h : Y ⊆ Σ) : Σ ∩ Y = Y := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨h hx, hx⟩

theorem finite_intersection_card_eq_of_contained
    {α : Type*} [DecidableEq α] {Y Σ : Finset α} (h : Y ⊆ Σ) :
    (Σ ∩ Y).card = Y.card := by
  have hEq : Σ ∩ Y = Y := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨h hx, hx⟩
  rw [hEq]

theorem zero_codim_not_positive {n : ℕ} (hn : 0 < n) : (0 : ℕ) ≠ n := by
  omega

theorem no_bool_embedding_into_fin_one :
    ¬ ∃ f : Bool → Fin 1, Function.Injective f := by
  rintro ⟨f, hf⟩
  have himage : f false = f true := Subsingleton.elim _ _
  have hfalse : (false : Bool) = true := hf himage
  exact (by decide : (false : Bool) ≠ true) hfalse

theorem principal_one_section_cannot_embed_two_points
    (N : ℕ) (hN : N = 1) :
    N - 1 = 0 ∧ ¬ ∃ f : Bool → Fin N, Function.Injective f := by
  subst N
  exact ⟨by norm_num, no_bool_embedding_into_fin_one⟩

end Hodge

/-! ## Navier--Stokes: finite energy forbids finite-coordinate blow-up -/

namespace NavierStokes

theorem coordinateSq_le_totalSq
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) :
    (x i) ^ 2 ≤ ∑ j : ι, (x j) ^ 2 := by
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg (x j))
    (Finset.mem_univ i)

theorem coordinateSq_le_energy
    {τ ι : Type*} [Fintype ι]
    (x : τ → ι → ℝ) (E : ℝ)
    (henergy : ∀ t, (∑ j : ι, (x t j) ^ 2) ≤ E) :
    ∀ t i, (x t i) ^ 2 ≤ E := by
  intro t i
  exact (coordinateSq_le_totalSq (x t) i).trans (henergy t)

theorem noCoordinateSqUnbounded_of_energyBound
    {τ ι : Type*} [Fintype ι]
    (x : τ → ι → ℝ) (E : ℝ)
    (henergy : ∀ t, (∑ j : ι, (x t j) ^ 2) ≤ E) :
    ¬ ∃ i : ι, ∀ M : ℝ, ∃ t : τ, M < (x t i) ^ 2 := by
  rintro ⟨i, hi⟩
  obtain ⟨t, ht⟩ := hi E
  have hle : (x t i) ^ 2 ≤ E := coordinateSq_le_energy x E henergy t i
  linarith

end NavierStokes

/-! ## Yang--Mills: chirality-ratio firewall -/

namespace YangMills

def chiralityRatio (plus minus : ℝ) : ℝ :=
  minus ^ 2 / (plus ^ 2 + minus ^ 2)

theorem selfDual_ratio_zero (plus : ℝ) : chiralityRatio plus 0 = 0 := by
  simp [chiralityRatio]

theorem antiSelfDual_ratio_one {minus : ℝ} (hminus : minus ≠ 0) :
    chiralityRatio 0 minus = 1 := by
  have hminusSq : minus ^ 2 ≠ 0 := pow_ne_zero 2 hminus
  simp [chiralityRatio, hminusSq]

theorem antiSelfDual_not_ratio_zero {minus : ℝ} (hminus : minus ≠ 0) :
    chiralityRatio 0 minus ≠ 0 := by
  rw [antiSelfDual_ratio_one hminus]
  norm_num

theorem localizedSpike_smallIntegral_maxRatio {ε : ℝ} (hε : 0 < ε) :
    ∃ mass plus minus : ℝ,
      0 < mass ∧ mass * minus ^ 2 < ε ∧ chiralityRatio plus minus = 1 := by
  refine ⟨ε / 2, 0, 1, ?_, ?_, ?_⟩
  · linarith
  · norm_num
    linarith
  · norm_num [chiralityRatio]

end YangMills

/-! ## Seventh object: cycle-safe inversion / retraction -/

namespace SeventhObject

/-- An abstract one-way-safe transfer.  `forward` embeds source objects into a
target, `backward` recovers them, and target algebraicity descends under the
backward map. -/
structure SafeRetract (A B : Type*) where
  sourceAlgebraic : A → Prop
  targetAlgebraic : B → Prop
  forward : A → B
  backward : B → A
  retract : ∀ a, backward (forward a) = a
  backward_preserves_algebraic :
    ∀ b, targetAlgebraic b → sourceAlgebraic (backward b)

theorem forward_preserves_nonalgebraicity
    {A B : Type*} (T : SafeRetract A B) {a : A}
    (ha : ¬ T.sourceAlgebraic a) :
    ¬ T.targetAlgebraic (T.forward a) := by
  intro htarget
  apply ha
  rw [← T.retract a]
  exact T.backward_preserves_algebraic (T.forward a) htarget

/-- A class-level scalar recovery modulo algebraic classes is enough for a safe
one-way transfer. -/
theorem scalar_recovery_mod_algebraic
    {V W : Type*} [AddCommGroup V] [Module ℚ V]
    (AlgV : V → Prop)
    (hadd : ∀ {x y}, AlgV x → AlgV y → AlgV (x + y))
    (hsmul : ∀ (q : ℚ) {x}, AlgV x → AlgV (q • x))
    (T : V → W) (S : W → V)
    (AlgW : W → Prop)
    (hS : ∀ {w}, AlgW w → AlgV (S w))
    {a correction : V} {q : ℚ}
    (hq : q ≠ 0)
    (hrec : S (T a) = q • a + correction)
    (hcorr : AlgV correction)
    (ha : ¬ AlgV a) :
    ¬ AlgW (T a) := by
  intro hTa
  have hST : AlgV (S (T a)) := hS hTa
  have hqa : AlgV (q • a) := by
    have hnegcorr : AlgV ((-1 : ℚ) • correction) := hsmul (-1) hcorr
    have hsum : AlgV (S (T a) + ((-1 : ℚ) • correction)) := hadd hST hnegcorr
    have heq : S (T a) + ((-1 : ℚ) • correction) = q • a := by
      rw [hrec]
      module
    rwa [heq] at hsum
  have hqinv : AlgV (q⁻¹ • (q • a)) := hsmul q⁻¹ hqa
  apply ha
  simpa [smul_smul, hq] using hqinv

end SeventhObject

/-! ## Cross-problem convergence and closed-limit transfer -/

namespace CrossProblem

variable {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]

theorem geometric_steps_tendsto
    (u : ℕ → X) (r C : ℝ)
    (hr : r < 1)
    (hstep : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ C * r ^ n) :
    ∃ x : X, Tendsto u atTop (𝓝 x) := by
  have hcauchy : CauchySeq u := cauchySeq_of_le_geometric r C hr hstep
  exact cauchySeq_tendsto_of_complete hcauchy

theorem geometric_steps_tendsto_in_closed
    (K : Set X) (hK : IsClosed K)
    (u : ℕ → X) (r C : ℝ)
    (hr : r < 1)
    (hstep : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ C * r ^ n)
    (hmem : ∀ n : ℕ, u n ∈ K) :
    ∃ x : X, x ∈ K ∧ Tendsto u atTop (𝓝 x) := by
  obtain ⟨x, hx⟩ := geometric_steps_tendsto u r C hr hstep
  refine ⟨x, ?_, hx⟩
  exact hK.mem_of_tendsto hx (Eventually.of_forall hmem)

end CrossProblem

/-! ## A single executable certificate -/

/-- The exact finite theorem bank assembled in this standalone file. -/
structure UnifiedBankCertificate : Prop where
  rhBregman : ∀ a b : ℝ, 0 ≤ RH.bregmanResidual a b
  rhAbel : ∀ (energy weight : ℕ → ℝ) (n : ℕ),
    (∑ i in range (n + 1), weight i * (energy (i + 1) - energy i)) =
      weight n * energy (n + 1) - weight 0 * energy 0 +
        ∑ i in range n, (weight i - weight (i + 1)) * energy (i + 1)
  pnpLedger : ∀ n : ℕ,
    Fintype.card (PNP.LayerNode n) = (n + 1) * 2 ∧
      Fintype.card (PNP.ChoiceWalk n) = 2 ^ n
  pnpLocalGlobalCounterexample :
    (∀ i : Fin 2, ∃ w : PNP.ChoiceWalk 2,
      PNP.correlated2 w ∧ w i = PNP.mixed2 i) ∧ ¬ PNP.correlated2 PNP.mixed2
  bsdDimensionGap : BSD.fiberPowerDim 1 1 2 = 3 ∧ BSD.fiberPowerDim 1 1 2 ≠ 4
  bsdMinusEigenspaceCounterexample :
    ∃ x : ℝ, x ≠ 0 ∧ BSD.signInvolution x = -x
  hodgeContainment : ∀ {α : Type*} {Y Σ : Set α}, Y ⊆ Σ → Σ ∩ Y = Y
  hodgeNoP0Embedding : ¬ ∃ f : Bool → Fin 1, Function.Injective f
  nsFiniteEnergyFirewall :
    ∀ {τ ι : Type*} [Fintype ι]
      (x : τ → ι → ℝ) (E : ℝ),
      (∀ t, (∑ j : ι, (x t j) ^ 2) ≤ E) →
      ¬ ∃ i : ι, ∀ M : ℝ, ∃ t : τ, M < (x t i) ^ 2
  ymASDRatio : ∀ {minus : ℝ}, minus ≠ 0 → YangMills.chiralityRatio 0 minus = 1
  seventhObjectSafe :
    ∀ {A B : Type*} (T : SeventhObject.SafeRetract A B) {a : A},
      (¬ T.sourceAlgebraic a) → ¬ T.targetAlgebraic (T.forward a)

/-- The requested single runnable bank statement. -/
theorem unified_executable_bank : UnifiedBankCertificate := by
  refine
    { rhBregman := RH.bregmanResidual_nonneg
      rhAbel := RH.weighted_energy_abel
      pnpLedger := ?_
      pnpLocalGlobalCounterexample := PNP.all_local_extensions_do_not_force_global
      bsdDimensionGap := BSD.doubleFiberProduct_dimension_gap
      bsdMinusEigenspaceCounterexample := BSD.minus_one_eigenspace_does_not_force_zero
      hodgeContainment := ?_
      hodgeNoP0Embedding := Hodge.no_bool_embedding_into_fin_one
      nsFiniteEnergyFirewall := ?_
      ymASDRatio := ?_
      seventhObjectSafe := ?_ }
  · intro n
    exact ⟨PNP.layerNode_card n, PNP.choiceWalk_card n⟩
  · intro α Y Σ h
    exact Hodge.intersection_eq_of_contained h
  · intro τ ι inst x E henergy
    exact NavierStokes.noCoordinateSqUnbounded_of_energyBound x E henergy
  · intro minus hminus
    exact YangMills.antiSelfDual_ratio_one hminus
  · intro A B T a ha
    exact SeventhObject.forward_preserves_nonalgebraicity T ha

/-! The official Clay statements are intentionally abstract here: this file does
not smuggle their conclusions in as definitions or axioms. -/
structure ClayClaims where
  rh : Prop
  pnp : Prop
  bsd : Prop
  hodge : Prop
  navierStokes : Prop
  yangMills : Prop

def AllSix (C : ClayClaims) : Prop :=
  C.rh ∧ C.pnp ∧ C.bsd ∧ C.hodge ∧ C.navierStokes ∧ C.yangMills

structure OfficialSolutionCertificate (C : ClayClaims) : Prop where
  rh : C.rh
  pnp : C.pnp
  bsd : C.bsd
  hodge : C.hodge
  navierStokes : C.navierStokes
  yangMills : C.yangMills

theorem allSix_iff_certificate (C : ClayClaims) :
    AllSix C ↔ OfficialSolutionCertificate C := by
  constructor
  · rintro ⟨hrh, hpnp, hbsd, hhodge, hns, hym⟩
    exact ⟨hrh, hpnp, hbsd, hhodge, hns, hym⟩
  · rintro ⟨hrh, hpnp, hbsd, hhodge, hns, hym⟩
    exact ⟨hrh, hpnp, hbsd, hhodge, hns, hym⟩

/-- Honesty firewall: the executable finite bank exists independently of any
placeholder assignment to the six official propositions.  This theorem is not
an independence result about mathematics; it only prevents a propositional
sleight of hand from being mistaken for a Clay proof. -/
theorem bank_coexists_with_no_placeholder_fire :
    UnifiedBankCertificate ∧
      ∃ C : ClayClaims,
        ¬ C.rh ∧ ¬ C.pnp ∧ ¬ C.bsd ∧ ¬ C.hodge ∧
          ¬ C.navierStokes ∧ ¬ C.yangMills := by
  refine ⟨unified_executable_bank, ?_⟩
  refine ⟨{ rh := False, pnp := False, bsd := False, hodge := False,
      navierStokes := False, yangMills := False }, ?_⟩
  simp

#print axioms unified_executable_bank
#print axioms allSix_iff_certificate
#print axioms bank_coexists_with_no_placeholder_fire
#print axioms SeventhObject.forward_preserves_nonalgebraicity
#print axioms SeventhObject.scalar_recovery_mod_algebraic
#print axioms CrossProblem.geometric_steps_tendsto_in_closed

end Millennium.Unified
