import Mathlib

namespace Millennium.YangMills

abbrev ParabolicJet3NA := ℝ × ℝ

def jetCompNA (outer inner : ParabolicJet3NA) : ParabolicJet3NA :=
  (outer.1 + inner.1,
    outer.2 + inner.2 + 2 * outer.1 * inner.1)

def jetInvNA (j : ParabolicJet3NA) : ParabolicJet3NA :=
  (-j.1, 2 * j.1^2 - j.2)

/-- Third-order jet of `h_out^{-1} ∘ sigma ∘ h_in`. -/
def nonautonomousJetStepNA
    (hIn hOut sigma : ParabolicJet3NA) : ParabolicJet3NA :=
  jetCompNA (jetInvNA hOut) (jetCompNA sigma hIn)

/-- Exact coefficient formula for a step written in different unit-tangent
coordinates at its two endpoints. -/
theorem nonautonomousJetStepNA_coefficients
    (a d A D b c : ℝ) :
    nonautonomousJetStepNA (a, d) (A, D) (b, c) =
      (b + a - A,
        c + d - D + 2 * a * b + 2 * A^2 - 2 * A * (a + b)) := by
  apply Prod.ext
  · simp [nonautonomousJetStepNA, jetCompNA, jetInvNA]
    ring
  · simp [nonautonomousJetStepNA, jetCompNA, jetInvNA]
    ring

/-- A cubic change between consecutive coordinates shifts the cubic coefficient
of one individual reduced step. -/
theorem cubic_coordinate_drift_shifts_individual_step_NA
    (d D b c : ℝ) :
    nonautonomousJetStepNA (0, d) (0, D) (b, c) =
      (b, c + d - D) := by
  simpa using nonautonomousJetStepNA_coefficients 0 d 0 D b c

/-- The autonomous special case preserves the full parabolic cubic jet. -/
theorem autonomousJetStep_preserves_twoLoopJet_NA
    (h sigma : ParabolicJet3NA) :
    nonautonomousJetStepNA h h sigma = sigma := by
  rcases h with ⟨a, d⟩
  rcases sigma with ⟨b, c⟩
  apply Prod.ext
  · simp [nonautonomousJetStepNA, jetCompNA, jetInvNA]
  · simp [nonautonomousJetStepNA, jetCompNA, jetInvNA]
    ring

/-- The middle coordinate cancels exactly under two consecutive nonautonomous
steps, leaving only endpoint coordinates around the two standard steps. -/
theorem nonautonomousJet_twoStep_middle_cancels_NA
    (h0 h1 h2 sigma0 sigma1 : ParabolicJet3NA) :
    jetCompNA
        (nonautonomousJetStepNA h1 h2 sigma1)
        (nonautonomousJetStepNA h0 h1 sigma0) =
      nonautonomousJetStepNA h0 h2
        (jetCompNA sigma1 sigma0) := by
  rcases h0 with ⟨a0, d0⟩
  rcases h1 with ⟨a1, d1⟩
  rcases h2 with ⟨a2, d2⟩
  rcases sigma0 with ⟨b0, c0⟩
  rcases sigma1 with ⟨b1, c1⟩
  apply Prod.ext
  · simp [nonautonomousJetStepNA, jetCompNA, jetInvNA]
    ring
  · simp [nonautonomousJetStepNA, jetCompNA, jetInvNA]
    ring

#print axioms nonautonomousJetStepNA_coefficients
#print axioms cubic_coordinate_drift_shifts_individual_step_NA
#print axioms autonomousJetStep_preserves_twoLoopJet_NA
#print axioms nonautonomousJet_twoStep_middle_cancels_NA

end Millennium.YangMills
