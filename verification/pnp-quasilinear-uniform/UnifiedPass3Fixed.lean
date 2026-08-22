import Mathlib

namespace Millennium
namespace UnifiedPass3

namespace HodgeCore

theorem cycle_compatible_transfer
    {ZX ZY HX HY : Type} (clX : ZX → HX) (clY : ZY → HY)
    (includeH : HY → HX) (projectH : HX → HY) (projectZ : ZX → ZY)
    (alpha : HY) (hsection : projectH (includeH alpha) = alpha)
    (hcompat : ∀ z, projectH (clX z) = clY (projectZ z))
    (hnon : alpha ∉ Set.range clY) : includeH alpha ∉ Set.range clX := by
  rintro ⟨z, hz⟩
  apply hnon
  refine ⟨projectZ z, ?_⟩
  calc
    clY (projectZ z) = projectH (clX z) := (hcompat z).symm
    _ = projectH (includeH alpha) := by rw [hz]
    _ = alpha := hsection

theorem projector_exhaustion
    {Z H : Type} (cl : Z → H) (pH : H → H) (pZ : Z → Z) (alpha : H)
    (hfix : pH alpha = alpha) (hcompat : ∀ z, pH (cl z) = cl (pZ z))
    (hAlg : alpha ∈ Set.range cl) :
    alpha ∈ Set.range (fun z => cl (pZ z)) := by
  rcases hAlg with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  calc
    cl (pZ z) = pH (cl z) := (hcompat z).symm
    _ = pH alpha := by rw [hz]
    _ = alpha := hfix

theorem projector_algebraicity_iff
    {Z H : Type} (cl : Z → H) (pH : H → H) (pZ : Z → Z) (alpha : H)
    (hfix : pH alpha = alpha) (hcompat : ∀ z, pH (cl z) = cl (pZ z)) :
    alpha ∈ Set.range cl ↔ alpha ∈ Set.range (fun z => cl (pZ z)) := by
  constructor
  · exact projector_exhaustion cl pH pZ alpha hfix hcompat
  · rintro ⟨z, hz⟩
    exact ⟨pZ z, hz⟩
end HodgeCore

namespace NSCore

theorem critical_scaling (L lambda r : ℝ) (hL : L ≠ 0) :
    (L ^ 2 * lambda) * (r / L) ^ 2 = lambda * r ^ 2 := by
  field_simp [hL]

theorem twist_scaling (L q g v t : ℝ) (hL : L ≠ 0) :
    (L ^ 2 * q) * (L ^ 2 * g) * (v / L ^ 3) * (t / L ^ 2) =
      (q * g * v * t) / L := by
  field_simp [hL]

theorem no_uniform_charge (J c : ℝ) (hJ : 0 < J) (hc : 0 < c) :
    ∃ L : ℝ, 0 < L ∧ J / L < c := by
  let L := J / c + 1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  rw [div_lt_iff₀ hL]
  dsimp [L]
  field_simp [ne_of_gt hc]
  nlinarith

theorem helicity_reversal {ell m h : ℝ}
    (he : 0 < ell) (hem : ell < m) (hmh : m < h) :
    (m - ell) / (h - ell) < m / h ∧ m / h < (m + ell) / (h + ell) := by
  have hh : 0 < h := lt_trans (lt_trans he hem) hmh
  have hhe : 0 < h - ell := sub_pos.mpr (lt_trans hem hmh)
  have hhp : 0 < h + ell := add_pos hh he
  constructor
  · apply (div_lt_div_iff₀ hhe hh).2
    nlinarith [mul_pos he (sub_pos.mpr hmh)]
  · apply (div_lt_div_iff₀ hh hhp).2
    nlinarith [mul_pos he (sub_pos.mpr hmh)]
end NSCore

namespace YMCore

theorem cumulative_budget (m d : ℕ → ℝ)
    (hstep : ∀ k, m (k + 1) ≥ m k - d k) :
    ∀ n, m n ≥ m 0 - ∑ k ∈ Finset.range n, d k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := hstep n
      rw [Finset.sum_range_succ]
      linarith

theorem gap_survives_margin (d0 d dN loss : ℝ)
    (hp : d0 - loss ≤ dN) (hl : loss ≤ d0 - d) : d ≤ dN := by
  linarith

theorem summable_defect_can_close_gap :
    ∃ d0 loss d1 : ℝ, 0 < d0 ∧ 0 ≤ loss ∧ d0 - loss ≤ d1 ∧ ¬ 0 < d1 := by
  refine ⟨1, 1, 0, ?_, ?_, ?_, ?_⟩ <;> norm_num

theorem fixed_time_contraction_implies_gap (Lambda c m tau : ℝ)
    (ht : 0 < tau)
    (hc : Real.exp (-m * tau) ≤ Real.exp (-(c * Lambda) * tau)) :
    c * Lambda ≤ m := by
  have hlin : -m * tau ≤ -(c * Lambda) * tau := (Real.exp_le_exp).mp hc
  by_contra hnot
  have hlt : m < c * Lambda := lt_of_not_ge hnot
  have hp : 0 < (c * Lambda - m) * tau :=
    mul_pos (sub_pos.mpr hlt) ht
  nlinarith

theorem quadratic_margin_step (rho r q q' E : ℝ)
    (hrho : 0 ≤ rho) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (hqb : q ≤ rho * r) (hp : q' ≤ q ^ 2 + E)
    (hE : E ≤ (rho - rho ^ 2) * r ^ 2) : q' ≤ rho * r ^ 2 := by
  have hrr : 0 ≤ rho * r := mul_nonneg hrho hr
  have hsq : q ^ 2 ≤ (rho * r) ^ 2 := by nlinarith
  calc
    q' ≤ q ^ 2 + E := hp
    _ ≤ (rho * r) ^ 2 + (rho - rho ^ 2) * r ^ 2 := add_le_add hsq hE
    _ = rho * r ^ 2 := by ring
end YMCore

structure ExactPass3 : Prop where
  hodgeProjector : ∀ {Z H : Type} (cl : Z → H) (pH : H → H)
    (pZ : Z → Z) (a : H), pH a = a →
      (∀ z, pH (cl z) = cl (pZ z)) →
      (a ∈ Set.range cl ↔ a ∈ Set.range (fun z => cl (pZ z)))
  nsScaling : ∀ L lambda r : ℝ, L ≠ 0 →
    (L ^ 2 * lambda) * (r / L) ^ 2 = lambda * r ^ 2
  nsNoUniformCharge : ∀ J c : ℝ, 0 < J → 0 < c →
    ∃ L : ℝ, 0 < L ∧ J / L < c
  ymBudget : ∀ m d : ℕ → ℝ, (∀ k, m (k + 1) ≥ m k - d k) →
    ∀ n, m n ≥ m 0 - ∑ k ∈ Finset.range n, d k
  ymCounterexample : ∃ d0 loss d1 : ℝ,
    0 < d0 ∧ 0 ≤ loss ∧ d0 - loss ≤ d1 ∧ ¬ 0 < d1

theorem exactPass3 : ExactPass3 := {
  hodgeProjector := HodgeCore.projector_algebraicity_iff
  nsScaling := NSCore.critical_scaling
  nsNoUniformCharge := NSCore.no_uniform_charge
  ymBudget := YMCore.cumulative_budget
  ymCounterexample := YMCore.summable_defect_can_close_gap }

end UnifiedPass3
end Millennium
