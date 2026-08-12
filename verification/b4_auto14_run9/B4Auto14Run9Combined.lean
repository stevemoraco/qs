import Mathlib

namespace B4Auto14Run9.RH

theorem model_cancellation_error_bound
    {D O A eD eO εD εO : ℝ}
    (hD : D = A + eD)
    (hO : O = -A + eO)
    (heD : |eD| ≤ εD)
    (heO : |eO| ≤ εO) :
    |D + O| ≤ εD + εO := by
  rw [hD, hO]
  have hcancel : A + eD + (-A + eO) = eD + eO := by ring
  rw [hcancel]
  have hd := abs_le.mp heD
  have ho := abs_le.mp heO
  apply abs_le.mpr
  constructor <;> linarith

theorem leading_cancellation_without_error_control_counterexample
    (M : ℝ) :
    ∃ D O A eD eO : ℝ,
      D = A + eD ∧
      O = -A + eO ∧
      D + O = 2 * M := by
  refine ⟨M, M, 0, M, M, ?_, ?_, ?_⟩ <;> ring

theorem exact_model_cancellation
    {D O A : ℝ}
    (hD : D = A)
    (hO : O = -A) :
    D + O = 0 := by
  rw [hD, hO]
  ring

#print axioms model_cancellation_error_bound
#print axioms leading_cancellation_without_error_control_counterexample
#print axioms exact_model_cancellation
end B4Auto14Run9.RH

namespace B4Auto14Run9.PNP

theorem bounded_incidence_compression
    {n χ d Δ q g : ℝ}
    (hχ : χ ≤ (d - 1) * Δ + 1)
    (hq : q ≤ χ + 4)
    (hg : g ≤ 2 * n + 2 * q - 2) :
    g ≤ 2 * n + 2 * (d - 1) * Δ + 8 := by
  linarith

theorem compression_kills_stronger_lower_bound
    {n χ d Δ q g : ℝ}
    (hχ : χ ≤ (d - 1) * Δ + 1)
    (hq : q ≤ χ + 4)
    (hg : g ≤ 2 * n + 2 * q - 2)
    (hlb : 2 * n + 2 * (d - 1) * Δ + 8 < g) : False := by
  have hub := bounded_incidence_compression hχ hq hg
  linarith

theorem triple_witness_compression
    {n χ Δ q g : ℝ}
    (hχ : χ ≤ 2 * Δ + 1)
    (hq : q ≤ χ + 4)
    (hg : g ≤ 2 * n + 2 * q - 2) :
    g ≤ 2 * n + 4 * Δ + 8 := by
  linarith

#print axioms bounded_incidence_compression
#print axioms compression_kills_stronger_lower_bound
#print axioms triple_witness_compression
end B4Auto14Run9.PNP

namespace B4Auto14Run9.BSD

theorem kurihara_certificate_to_imc
    {Cert IMC : Prop}
    (hiff : Cert ↔ IMC)
    (hcert : Cert) : IMC :=
  hiff.mp hcert

theorem imc_alone_not_full_bsd_countermodel :
    ∃ (IMC RankEq ShaFinite GPR Bockstein : Prop),
      IMC ∧
      ¬ (IMC ∧ RankEq ∧ ShaFinite ∧ GPR ∧ Bockstein) := by
  refine ⟨True, False, True, True, True, ?_⟩
  simp

theorem certificate_plus_descent_gates
    {Cert IMC RankEq ShaFinite GPR Bockstein : Prop}
    (hiff : Cert ↔ IMC)
    (hcert : Cert)
    (hrank : RankEq)
    (hsha : ShaFinite)
    (hgpr : GPR)
    (hbock : Bockstein) :
    IMC ∧ RankEq ∧ ShaFinite ∧ GPR ∧ Bockstein := by
  exact ⟨hiff.mp hcert, hrank, hsha, hgpr, hbock⟩

#print axioms kurihara_certificate_to_imc
#print axioms imc_alone_not_full_bsd_countermodel
#print axioms certificate_plus_descent_gates
end B4Auto14Run9.BSD

namespace B4Auto14Run9.Hodge

theorem factorization_closes_algebraicity
    {α : Type*}
    (Alg : α → Prop)
    (comp : α → α → α)
    (P A Q Y : α)
    (hY : Y = comp P (comp A Q))
    (hcomp : ∀ X Z, Alg X → Alg Z → Alg (comp X Z))
    (hP : Alg P)
    (hA : Alg A)
    (hQ : Alg Q) : Alg Y := by
  rw [hY]
  exact hcomp P (comp A Q) hP (hcomp A Q hA hQ)

theorem positivity_not_lowering_countermodel :
    ∃ (HodgeTypePositive LoweringFactorization : Prop),
      HodgeTypePositive ∧ ¬ LoweringFactorization := by
  exact ⟨True, False, trivial, by simp⟩

theorem lowering_factorization_terminal_rule
    {Factorization Algebraic : Prop}
    (hclose : Factorization → Algebraic)
    (hfactor : Factorization) : Algebraic :=
  hclose hfactor

#print axioms factorization_closes_algebraicity
#print axioms positivity_not_lowering_countermodel
#print axioms lowering_factorization_terminal_rule
end B4Auto14Run9.Hodge

namespace B4Auto14Run9.NS

theorem endpoint_no_pressure_cutoff_window :
    ¬ ∃ β : ℚ, β < (3 : ℚ) / 8 ∧ (23 : ℚ) / 48 < β := by
  rintro ⟨β, hinit, hpressure⟩
  linarith

theorem endpoint_no_cubic_cutoff_window :
    ¬ ∃ β : ℚ, β < (3 : ℚ) / 8 ∧ (7 : ℚ) / 16 < β := by
  rintro ⟨β, hinit, hcubic⟩
  linarith

theorem endpoint_enstrophy_misses_repaired_threshold :
    ¬ ((1 : ℚ) / 4 < (1 : ℚ) / 5) := by
  norm_num

theorem endpoint_pair_violates_joint_threshold :
    ¬ (8 * ((1 : ℚ) / 2) + 9 * ((1 : ℚ) / 4) < 5) := by
  norm_num

#print axioms endpoint_no_pressure_cutoff_window
#print axioms endpoint_no_cubic_cutoff_window
#print axioms endpoint_enstrophy_misses_repaired_threshold
#print axioms endpoint_pair_violates_joint_threshold
end B4Auto14Run9.NS

namespace B4Auto14Run9.YM

theorem spectral_tail_finite_witness
    {q r C m moment : ℝ} {n : ℕ}
    (hlower : r ^ n * m ≤ moment)
    (hupper : moment ≤ C * q ^ n)
    (hseparate : C * q ^ n < r ^ n * m) : False := by
  linarith

theorem one_visible_sector_not_full_gap_countermodel :
    ∃ visible hidden q : ℝ,
      0 < q ∧
      visible ≤ q ∧
      ¬ q ≤ hidden := by
  refine ⟨0, 0, 1, ?_⟩
  norm_num

theorem common_ceiling_is_uniform
    {α : Type*} {BoundedByQ : α → Prop}
    (hall : ∀ ψ, BoundedByQ ψ) (ψ : α) : BoundedByQ ψ :=
  hall ψ

#print axioms spectral_tail_finite_witness
#print axioms one_visible_sector_not_full_gap_countermodel
#print axioms common_ceiling_is_uniform
end B4Auto14Run9.YM
