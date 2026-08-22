import Mathlib

/-!
# Millennium Braid current unconditional frontier

This file contains only unconditional finite/functional theorems and an exact
logical firewall. It does not assert any unresolved Clay conclusion.
-/

open Filter
open scoped BigOperators

namespace MillenniumBraidCurrentFrontier

/-! ## Closed-limit and unconditional convergence layer -/

variable {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]

/-- Geometrically decaying consecutive increments force full-sequence
convergence in a complete metric space. -/
theorem geometricStepsTendsto
    (u : ℕ → X) (r C : ℝ)
    (hr : r < 1)
    (hstep : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ C * r ^ n) :
    ∃ x : X, Tendsto u atTop (𝓝 x) := by
  have hcauchy : CauchySeq u :=
    cauchySeq_of_le_geometric r C hr hstep
  exact cauchySeq_tendsto_of_complete hcauchy

/-- Summably controlled consecutive increments force full-sequence
convergence in a complete metric space. -/
theorem summableStepsTendsto
    (u : ℕ → X) (d : ℕ → ℝ)
    (hstep : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ d n)
    (hsum : Summable d) :
    ∃ x : X, Tendsto u atTop (𝓝 x) := by
  have hcauchy : CauchySeq u :=
    cauchySeq_of_dist_le_of_summable d hstep hsum
  exact cauchySeq_tendsto_of_complete hcauchy

/-- A closed native admissibility class contains the limit constructed from
summably controlled steps. -/
theorem summableStepsTendstoInClosed
    (K : Set X) (hK : IsClosed K)
    (u : ℕ → X) (d : ℕ → ℝ)
    (hstep : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ d n)
    (hsum : Summable d)
    (hmem : ∀ n : ℕ, u n ∈ K) :
    ∃ x : X, x ∈ K ∧ Tendsto u atTop (𝓝 x) := by
  obtain ⟨x, hx⟩ := summableStepsTendsto u d hstep hsum
  refine ⟨x, ?_, hx⟩
  exact hK.mem_of_tendsto hx (Eventually.of_forall hmem)

/-- A uniform closed lower margin on real approximants survives the geometric
limit constructed above. -/
theorem geometricRealLowerMargin
    (u : ℕ → ℝ) (r C margin : ℝ)
    (hr : r < 1)
    (hstep : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ C * r ^ n)
    (hmargin : ∀ n : ℕ, margin ≤ u n) :
    ∃ x : ℝ, margin ≤ x ∧ Tendsto u atTop (𝓝 x) := by
  obtain ⟨x, hx⟩ := geometricStepsTendsto u r C hr hstep
  refine ⟨x, ?_, hx⟩
  exact isClosed_Ici.mem_of_tendsto hx (Eventually.of_forall hmargin)

/-! ## Positive-part charging and grouping -/

variable {W S B A : Type*} [Fintype W] [Fintype S] [Fintype B] [Fintype A]

/-- Positive part after summation is bounded by atomized positive parts. -/
theorem maxZeroSumLeSumMaxZero (f : S → ℝ) :
    max 0 (∑ s, f s) ≤ ∑ s, max 0 (f s) := by
  apply max_le
  · exact Finset.sum_nonneg (fun s _ => le_max_left 0 (f s))
  · exact Finset.sum_le_sum (fun s _ => le_max_right 0 (f s))

/-- Nonnegative weights preserve positive-part charging. -/
theorem weightedPositivePartCharging
    (weight : W → ℝ)
    (term : W → S → ℝ)
    (hweight : ∀ w, 0 ≤ weight w) :
    ∑ w, weight w * max 0 (∑ s, term w s)
      ≤ ∑ s, ∑ w, weight w * max 0 (term w s) := by
  calc
    ∑ w, weight w * max 0 (∑ s, term w s)
        ≤ ∑ w, weight w * ∑ s, max 0 (term w s) := by
          apply Finset.sum_le_sum
          intro w _
          exact mul_le_mul_of_nonneg_left
            (maxZeroSumLeSumMaxZero (term w)) (hweight w)
    _ = ∑ w, ∑ s, weight w * max 0 (term w s) := by
          apply Finset.sum_congr rfl
          intro w _
          rw [Finset.mul_sum]
    _ = ∑ s, ∑ w, weight w * max 0 (term w s) := by
          rw [Finset.sum_comm]

/-- Grouping before taking positive parts can only retain more cancellation. -/
theorem groupedMaxZeroLe (f : B → A → ℝ) :
    max 0 (∑ b, ∑ a, f b a) ≤ ∑ b, max 0 (∑ a, f b a) := by
  exact maxZeroSumLeSumMaxZero (fun b => ∑ a, f b a)

/-- Weighted grouped charging is bounded by charging each group separately. -/
theorem weightedGroupedCharging
    (w : W → ℝ) (f : W → B → A → ℝ) (hw : ∀ x, 0 ≤ w x) :
    ∑ x, w x * max 0 (∑ b, ∑ a, f x b a) ≤
      ∑ b, ∑ x, w x * max 0 (∑ a, f x b a) := by
  exact weightedPositivePartCharging w (fun x b => ∑ a, f x b a) hw

/-! ## Recurrent-return depletion cocycle -/

/-- A fixed positive charge paid on each selected return interval telescopes
against a nonnegative budget. -/
theorem finiteReturnDepletion
    (n : ℕ)
    (budget error : ℕ → ℝ)
    (c δ : ℝ)
    (hstep : ∀ k : ℕ,
      budget (k + 1) + c * δ ≤ budget k + error k)
    (hterminal : 0 ≤ budget n) :
    Finset.sum (Finset.range n) (fun _ => c * δ) ≤
      budget 0 + Finset.sum (Finset.range n) error := by
  have htel :
      budget n + Finset.sum (Finset.range n) (fun _ => c * δ) ≤
        budget 0 + Finset.sum (Finset.range n) error := by
    clear hterminal
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := hstep n
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith
  linarith

/-- Infinitely many returns carrying one fixed positive charge are incompatible
with a nonnegative budget and uniformly bounded cumulative error. -/
theorem recurrentFixedChargeDepletionImpossible
    (budget error : ℕ → ℝ)
    (c δ E : ℝ)
    (hc : 0 < c)
    (hδ : 0 < δ)
    (hbudget : ∀ n : ℕ, 0 ≤ budget n)
    (hstep : ∀ k : ℕ,
      budget (k + 1) + c * δ ≤ budget k + error k)
    (herror : ∀ n : ℕ,
      Finset.sum (Finset.range n) error ≤ E) :
    False := by
  have hcharge : 0 < c * δ := mul_pos hc hδ
  obtain ⟨N, hN⟩ := exists_nat_gt ((budget 0 + E) / (c * δ))
  have hfinite := finiteReturnDepletion N budget error c δ hstep (hbudget N)
  have herr := herror N
  have hsum :
      Finset.sum (Finset.range N) (fun _ => c * δ) =
        (N : ℝ) * (c * δ) := by simp
  have hover : budget 0 + E < (N : ℝ) * (c * δ) :=
    (div_lt_iff₀ hcharge).mp hN
  rw [hsum] at hfinite
  linarith

/-- Observable form of recurrent depletion. -/
theorem recurrentObservableDepletionImpossible
    (budget activity error : ℕ → ℝ)
    (c δ E : ℝ)
    (hc : 0 < c)
    (hδ : 0 < δ)
    (hbudget : ∀ n : ℕ, 0 ≤ budget n)
    (hactivity : ∀ n : ℕ, δ ≤ activity n)
    (hstep : ∀ k : ℕ,
      budget (k + 1) + c * activity k ≤ budget k + error k)
    (herror : ∀ n : ℕ,
      Finset.sum (Finset.range n) error ≤ E) :
    False := by
  have hstepFixed : ∀ k : ℕ,
      budget (k + 1) + c * δ ≤ budget k + error k := by
    intro k
    have hmul : c * δ ≤ c * activity k :=
      mul_le_mul_of_nonneg_left (hactivity k) (le_of_lt hc)
    linarith [hstep k]
  exact recurrentFixedChargeDepletionImpossible
    budget error c δ E hc hδ hbudget hstepFixed herror

/-- Bounded cumulative error is load-bearing: one unit of error per return can
fund perpetual unit activity. -/
theorem unitErrorFundsPerpetualUnitReturns :
    ∃ budget error : ℕ → ℝ,
      (∀ n : ℕ, 0 ≤ budget n) ∧
      (∀ n : ℕ, budget (n + 1) + 1 ≤ budget n + error n) ∧
      (∀ n : ℕ, error n = 1) := by
  refine ⟨(fun _ => 0), (fun _ => 1), ?_, ?_, ?_⟩
  · intro n
    norm_num
  · intro n
    norm_num
  · intro n
    rfl

/-! ## Source-proof and endpoint-variation firewalls -/

/-- Long consecutive spike blocks defeat every positive reweighting retaining a
fixed critical mass fraction while claiming a uniform nonlinear prefix budget. -/
theorem longSpikeBlockReweightingNoGo
    (total oldMass spikeMass c C B : ℝ)
    (htotal : 0 < total)
    (hB : 0 ≤ B)
    (hold : oldMass ≤ (c / 2) * total)
    (hcritical : c * total ≤ oldMass + spikeMass)
    (hlarge : 2 * C < B * c)
    (hnonlinear : B * spikeMass ≤ C * total) :
    False := by
  have hspike : (c / 2) * total ≤ spikeMass := by
    linarith
  have hpay : B * ((c / 2) * total) ≤ B * spikeMass :=
    mul_le_mul_of_nonneg_left hspike hB
  have hover : C * total < B * ((c / 2) * total) := by
    have hscaled := mul_lt_mul_of_pos_right hlarge htotal
    nlinarith
  linarith

/-- Positive quotient saturation is incompatible with the ambient
quadratic-versus-cubic stationarity identity using the quotient value itself as
multiplier. The missing bridge is stationarity, not algebra. -/
theorem positiveQuotientSaturatorNotStationary
    (A J Λ : ℝ)
    (hA : 0 < A)
    (hΛ : 0 < Λ)
    (hSaturates : J = Λ * A) :
    3 * J ≠ 2 * Λ * A := by
  have hJ : 0 < J := by
    rw [hSaturates]
    exact mul_pos hΛ hA
  intro hStationary
  rw [hSaturates] at hStationary
  nlinarith

/-! ## Exact Clay-interface firewall -/

structure OfficialClayStatements where
  rh : Prop
  pNeNP : Prop
  bsd : Prop
  hodge : Prop
  navierStokes : Prop
  yangMills : Prop

namespace OfficialClayStatements

def All (S : OfficialClayStatements) : Prop :=
  S.rh ∧ S.pNeNP ∧ S.bsd ∧ S.hodge ∧ S.navierStokes ∧ S.yangMills

end OfficialClayStatements

/-- The finite theorem bank cannot, by pure packaging, prove every possible
assignment of truth values to six abstract interfaces. Problem-specific
reductions and native estimates are logically necessary. -/
theorem noUniversalClayConclusion :
    ¬ (∀ S : OfficialClayStatements, S.All) := by
  intro h
  have hfalse := h ⟨False, False, False, False, False, False⟩
  exact hfalse.1

/-- Mutual exclusivity does not select a true side. -/
theorem mutualExclusivityDoesNotChooseSide :
    ¬ (∀ A B : Prop, (A → ¬ B) → (B → ¬ A) → A ∨ B) := by
  intro h
  rcases h False False (fun hA => False.elim hA)
      (fun hB => False.elim hB) with hF | hF
  · exact hF
  · exact hF

/-- Refuting a proposed route does not prove its target. -/
theorem refutedRouteDoesNotProveTarget :
    ¬ (∀ A G : Prop, (A → G) → (¬ A) → G) := by
  intro h
  exact h False False (fun hA => False.elim hA) (fun hA => hA)

/-- A compact certificate object for the unconditional frontier proved above. -/
structure FrontierCertificate where
  geometricConvergence :
    ∀ {Y : Type*} [PseudoMetricSpace Y] [CompleteSpace Y]
      (u : ℕ → Y) (r C : ℝ),
      r < 1 →
      (∀ n : ℕ, dist (u n) (u (n + 1)) ≤ C * r ^ n) →
      ∃ x : Y, Tendsto u atTop (𝓝 x)
  summableConvergence :
    ∀ {Y : Type*} [PseudoMetricSpace Y] [CompleteSpace Y]
      (u : ℕ → Y) (d : ℕ → ℝ),
      (∀ n : ℕ, dist (u n) (u (n + 1)) ≤ d n) →
      Summable d →
      ∃ x : Y, Tendsto u atTop (𝓝 x)
  positivePartCharging :
    ∀ {I : Type*} [Fintype I] (f : I → ℝ),
      max 0 (∑ i, f i) ≤ ∑ i, max 0 (f i)
  noUniversalClay : ¬ (∀ S : OfficialClayStatements, S.All)

/-- Fully unconditional construction of the current cross-problem frontier
certificate. -/
def currentFrontierCertificate : FrontierCertificate where
  geometricConvergence := fun u r C hr hstep =>
    geometricStepsTendsto u r C hr hstep
  summableConvergence := fun u d hstep hsum =>
    summableStepsTendsto u d hstep hsum
  positivePartCharging := fun f => maxZeroSumLeSumMaxZero f
  noUniversalClay := noUniversalClayConclusion

/-- One unconditional executable statement for the latest frontier. It
constructs the finite/functional certificate and simultaneously records that
this certificate does not manufacture arbitrary Clay truth values. -/
theorem millenniumBraidCurrentUnconditionalFrontier :
    Nonempty FrontierCertificate ∧
    ¬ (∀ S : OfficialClayStatements, S.All) := by
  exact ⟨⟨currentFrontierCertificate⟩, noUniversalClayConclusion⟩

#print axioms geometricStepsTendsto
#print axioms summableStepsTendsto
#print axioms summableStepsTendstoInClosed
#print axioms geometricRealLowerMargin
#print axioms maxZeroSumLeSumMaxZero
#print axioms weightedPositivePartCharging
#print axioms groupedMaxZeroLe
#print axioms weightedGroupedCharging
#print axioms finiteReturnDepletion
#print axioms recurrentFixedChargeDepletionImpossible
#print axioms recurrentObservableDepletionImpossible
#print axioms unitErrorFundsPerpetualUnitReturns
#print axioms longSpikeBlockReweightingNoGo
#print axioms positiveQuotientSaturatorNotStationary
#print axioms noUniversalClayConclusion
#print axioms mutualExclusivityDoesNotChooseSide
#print axioms refutedRouteDoesNotProveTarget
#print axioms currentFrontierCertificate
#print axioms millenniumBraidCurrentUnconditionalFrontier

end MillenniumBraidCurrentFrontier
