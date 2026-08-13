import UnifiedEntrypoint

/-!
# Public replay for the newest unified-braid firewalls

This file byte-for-byte replays the new scalar and logical proof cores without
publishing the private RH-Lean module bank.  The `CompiledLedger` dependency was
already replayed successfully on the public repository.
-/

namespace UnifiedBraidPublicReplay

open MillenniumGrandAggregate

inductive Problem where
  | rh
  | pVersusNP
  | bsd
  | hodge
  | navierStokes
  | yangMills
  | poincare
  | inversion
  deriving DecidableEq, BEq, Repr

inductive ResearchStatus where
  | openProblem
  | solvedHumanBackground
  | researchObject
  | officialKernelVerified
  deriving DecidableEq, BEq, Repr

def status : Problem → ResearchStatus
  | .rh => .openProblem
  | .pVersusNP => .openProblem
  | .bsd => .openProblem
  | .hodge => .openProblem
  | .navierStokes => .openProblem
  | .yangMills => .openProblem
  | .poincare => .solvedHumanBackground
  | .inversion => .researchObject

theorem no_lane_silently_promoted :
    ∀ p : Problem, status p ≠ .officialKernelVerified := by
  intro p
  cases p <;> simp [status]

theorem scaled_margin_difference_identity
    {a b c d r s : ℝ}
    (hr : r ^ 2 = a)
    (hs : s ^ 2 = b - a)
    (hc : c ^ 2 = 1 - d ^ 2) :
    (r * c) ^ 2 - (s * d) ^ 2 = a - b * d ^ 2 := by
  nlinarith

theorem scaled_margin_pos_iff
    {a b c d r s : ℝ}
    (hr : r ^ 2 = a)
    (hs : s ^ 2 = b - a)
    (hc : c ^ 2 = 1 - d ^ 2)
    (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) :
    0 < r * c - s * d ↔ b * d ^ 2 < a := by
  have hrc : 0 ≤ r * c := mul_nonneg hr0 hc0
  have hsd : 0 ≤ s * d := mul_nonneg hs0 hd0
  have hid := scaled_margin_difference_identity hr hs hc
  constructor
  · intro h
    nlinarith [sq_nonneg (r * c + s * d)]
  · intro h
    by_contra hnot
    have hdiff : r * c - s * d ≤ 0 := le_of_not_gt hnot
    have hle : r * c ≤ s * d := by linarith
    nlinarith [sq_nonneg (r * c + s * d)]

theorem return_lobe_budget
    {P N e delta : ℝ}
    (hbudget : N + |e| ≤ (1 - delta) * P) :
    delta * P ≤ |(P - N) + e| := by
  have he : -|e| ≤ e := neg_abs_le e
  have hraw : delta * P ≤ (P - N) + e := by
    nlinarith
  exact hraw.trans (le_abs_self ((P - N) + e))

theorem complementary_lobes_cancel :
    ∃ P : ℝ, 0 < P ∧ P - P = 0 := by
  exact ⟨1, by norm_num, by norm_num⟩

theorem global_sign_preserves_response_magnitude
    {sigma x : ℝ} (hsigma : sigma = 1 ∨ sigma = -1) :
    |sigma * x| = |x| := by
  rcases hsigma with rfl | rfl <;> simp

theorem equivalence_needs_a_seed :
    ¬ (∀ A B : Prop, (A ↔ B) → A) := by
  intro h
  exact h False False Iff.rfl

theorem exclusivity_needs_exhaustivity :
    ¬ (∀ A B : Prop, ¬ (A ∧ B) → A ∨ B) := by
  intro h
  have hf : False ∨ False := h False False (by simp)
  exact hf.elim (fun x => x) (fun x => x)

structure PublicReplayStatement : Prop where
  priorLedger : CompiledLedger
  statusFirewall : ∀ p : Problem, status p ≠ .officialKernelVerified
  spectralIdentity : ∀ {a b c d r s : ℝ},
    r ^ 2 = a → s ^ 2 = b - a → c ^ 2 = 1 - d ^ 2 →
    (r * c) ^ 2 - (s * d) ^ 2 = a - b * d ^ 2
  sourceCancellationBudget : ∀ {P N e delta : ℝ},
    N + |e| ≤ (1 - delta) * P → delta * P ≤ |(P - N) + e|
  inversionFirewall : ¬ (∀ A B : Prop, (A ↔ B) → A)
  exclusivityFirewall : ¬ (∀ A B : Prop, ¬ (A ∧ B) → A ∨ B)

theorem public_replay_statement : PublicReplayStatement where
  priorLedger := MillenniumGrandExecutable.everything_discovered_one_gigantic_runnable_statement
  statusFirewall := no_lane_silently_promoted
  spectralIdentity := fun hr hs hc => scaled_margin_difference_identity hr hs hc
  sourceCancellationBudget := fun h => return_lobe_budget h
  inversionFirewall := equivalence_needs_a_seed
  exclusivityFirewall := exclusivity_needs_exhaustivity

#print axioms scaled_margin_difference_identity
#print axioms scaled_margin_pos_iff
#print axioms return_lobe_budget
#print axioms complementary_lobes_cancel
#print axioms global_sign_preserves_response_magnitude
#print axioms equivalence_needs_a_seed
#print axioms exclusivity_needs_exhaustivity
#print axioms public_replay_statement

end UnifiedBraidPublicReplay
