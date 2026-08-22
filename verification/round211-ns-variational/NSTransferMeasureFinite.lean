import Mathlib

/-!
# Round 211 transfer-measure and zero-output finite firewalls

This file formalizes only scalar concentration proxies, exact-versus-small
logic, and an omitted finite routing case. It does not formalize Radon measures,
Lebesgue integration, Biot--Savart operators, defect measures, compactness,
Navier--Stokes solutions, or the Clay problem.
-/

namespace Millennium
namespace Round211NavierStokes

/-- Lebesgue support-volume/error proxy for a unit spike on one cell among
`n+1` equally sized cells. -/
def supportVolumeProxy (n : ℕ) : ℚ :=
  1 / (((n + 1 : ℕ) : ℚ))

/-- A probability measure concentrating all mass on the spike sees unit
transfer at every index. -/
def concentratedTransferProxy (_n : ℕ) : ℚ := 1

/-- The support proxy is positive. -/
theorem support_volume_proxy_pos (n : ℕ) :
    0 < supportVolumeProxy n := by
  unfold supportVolumeProxy
  positivity

/-- The reciprocal support proxy has the exact shrinking-scale identity. -/
theorem support_volume_scale_identity (n : ℕ) :
    (((n + 1 : ℕ) : ℚ)) * supportVolumeProxy n = 1 := by
  rw [supportVolumeProxy]
  have hnonzero : (((n + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  field_simp [hnonzero]

/-- Concentrated transfer remains exactly one. -/
theorem concentrated_transfer_stays_one (n : ℕ) :
    concentratedTransferProxy n = 1 := by
  rfl

/-- At index one, bounded unit measure mass sees unit transfer although the
Lebesgue error/support proxy is only one half. -/
theorem bounded_measure_mass_does_not_dominate_lp_proxy :
    concentratedTransferProxy 1 > supportVolumeProxy 1 := by
  norm_num [concentratedTransferProxy, supportVolumeProxy]

/-- Exact finite countermodel to any universal inference that the concentrated
integral is bounded by the shrinking Lebesgue proxy. -/
theorem shrinking_lp_proxy_does_not_force_transfer_decay :
    ¬ (∀ n, concentratedTransferProxy n ≤ supportVolumeProxy n) := by
  intro h
  have hbad := h 1
  norm_num [concentratedTransferProxy, supportVolumeProxy] at hbad

/-- Scalar proxy for a bounded global `L^q` mass. -/
def globalQMass (_n : ℕ) : ℚ := 1

/-- The same entire `L^q` mass can sit on the shrinking support. -/
def localConcentratedQMass (_n : ℕ) : ℚ := 1

/-- A bounded global mass does not, by itself, make the mass on the shrinking
support small. -/
theorem bounded_global_mass_allows_full_local_concentration (n : ℕ) :
    globalQMass n = 1 ∧ localConcentratedQMass n = 1 ∧
      0 < supportVolumeProxy n := by
  exact ⟨rfl, rfl, support_volume_proxy_pos n⟩

/-- An arbitrarily small nonnegative scalar need not be exactly zero. -/
theorem small_output_does_not_imply_exact_zero
    (epsilon : ℚ) (hepsilon : 0 < epsilon) :
    ∃ x : ℚ, 0 < x ∧ x ≤ epsilon ∧ x ≠ 0 := by
  refine ⟨epsilon / 2, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

/-- Three scalar routing channels, with `none` representing a newly introduced
channel omitted from a two-channel ranking table. -/
def IsRankedChannel : Option Bool → Prop
  | none => False
  | some _ => True

/-- The two named channels are ranked while the omitted channel is not. -/
theorem finite_rank_table_omits_new_channel :
    IsRankedChannel (some false) ∧
    IsRankedChannel (some true) ∧
    ¬ IsRankedChannel none := by
  simp [IsRankedChannel]

/-- Ranking every listed channel does not rank an omitted channel. -/
theorem listed_channel_termination_does_not_cover_omitted_channel :
    (∀ b : Bool, IsRankedChannel (some b)) ∧
      ¬ IsRankedChannel none := by
  constructor
  · intro b
    cases b <;> simp [IsRankedChannel]
  · simp [IsRankedChannel]

#print axioms support_volume_proxy_pos
#print axioms support_volume_scale_identity
#print axioms concentrated_transfer_stays_one
#print axioms bounded_measure_mass_does_not_dominate_lp_proxy
#print axioms shrinking_lp_proxy_does_not_force_transfer_decay
#print axioms bounded_global_mass_allows_full_local_concentration
#print axioms small_output_does_not_imply_exact_zero
#print axioms finite_rank_table_omits_new_channel
#print axioms listed_channel_termination_does_not_cover_omitted_channel

end Round211NavierStokes
end Millennium
