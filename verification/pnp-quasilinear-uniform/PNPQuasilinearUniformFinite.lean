import Mathlib

namespace Millennium
namespace UnifiedPass2

namespace RHCore

def posPart (x : ℝ) := max x 0

noncomputable def energy (x : ℝ) := posPart x ^ 2 / 2

noncomputable def residual (a b : ℝ) := posPart b * (b - a) - (energy b - energy a)

theorem residual_nonneg (a b : ℝ) : 0 ≤ residual a b := by
  unfold residual energy posPart
  by_cases hb : 0 ≤ b
  · rw [max_eq_left hb]
    by_cases ha : 0 ≤ a
    · rw [max_eq_left ha]
      nlinarith [sq_nonneg (b - a)]
    · have ha' : a ≤ 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      nlinarith [mul_nonpos_of_nonpos_of_nonneg ha' hb]
  · have hb' : b ≤ 0 := le_of_not_ge hb
    rw [max_eq_right hb']
    by_cases ha : 0 ≤ a
    · rw [max_eq_left ha]
      nlinarith [sq_nonneg a]
    · have ha' : a ≤ 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      norm_num

theorem edge_identity (theta delta mu nu y : ℝ) :
    -(2 * theta + delta) * y + (theta - mu) * y + (theta - nu) * y =
      -(delta + mu + nu) * y := by ring

theorem abel_floor (delta mu nu omega : ℝ)
    (hd : 0 ≤ delta) (hm : 0 ≤ mu) (hn : 0 ≤ nu) :
    delta ^ 2 ≤ (delta + mu + nu) ^ 2 + omega ^ 2 := by
  have hmn : 0 ≤ mu + nu := add_nonneg hm hn
  have hc : 0 ≤ 2 * delta * (mu + nu) :=
    mul_nonneg (mul_nonneg (by norm_num) hd) hmn
  nlinarith [sq_nonneg (mu + nu), sq_nonneg omega]

theorem schur_residual (A B D y : ℝ) (hD : D ≠ 0) :
    A - B ^ 2 / D =
      (A - 2 * B * y + D * y ^ 2) - (D * y - B) ^ 2 / D := by
  field_simp [hD]
  ring

theorem exact_tail_residual (B D : ℝ) (hD : D ≠ 0) :
    D * (B / D) - B = 0 := by
  field_simp [hD]
  ring
end RHCore

namespace PNPCore

theorem sampling_bound : ((3 : ℚ) / 4) ^ 8 < (1 : ℚ) / 8 := by norm_num

theorem repetition (N L t : ℕ) (h : N + 1 ≤ (2 * L + 3) * t) :
    N < (2 * L + 3) * t := by omega

theorem padding (N ell M p : ℕ) (he : ell ≤ N) (hM : M ≤ 13 * N * ell) :
    M - p ≤ 13 * N * N := by
  calc
    M - p ≤ M := Nat.sub_le _ _
    _ ≤ 13 * N * ell := hM
    _ ≤ 13 * N * N := Nat.mul_le_mul_left (13 * N) he

theorem uniform_contrapositive
    (PEqNP Small Major : Prop) (hU : PEqNP → Small)
    (hE : Small → Major) (hL : ¬ Major) : ¬ PEqNP := by
  intro h
  exact hL (hE (hU h))

theorem eventual_majorant (h : ℕ → ℕ)
    (hg : ∀ C, ∃ n0, ∀ n, n0 ≤ n → C + 1 ≤ h n) (C : ℕ) :
    ∃ n0, ∀ n, n0 ≤ n → C < h n := by
  obtain ⟨n0, hn⟩ := hg C
  exact ⟨n0, fun n h0 => Nat.lt_of_succ_le (hn n h0)⟩

theorem absorb_multiplier (K b C H : ℕ) (hb : 1 ≤ b)
    (hK : K ≤ b) (hCH : C + 1 ≤ H) : K * b ^ C ≤ b ^ H := by
  calc
    K * b ^ C ≤ b * b ^ C := Nat.mul_le_mul_right (b ^ C) hK
    _ = b ^ (C + 1) := by simp [pow_succ, Nat.mul_comm]
    _ ≤ b ^ H := Nat.pow_le_pow_right (by omega) hCH

theorem one_child_lt_one (l r : ℚ) (h : (l + r) / 2 < 1) :
    l < 1 ∨ r < 1 := by
  by_contra hn
  push Not at hn
  linarith

theorem terminal_potential_zero (n : ℕ) (h : (n : ℚ) < 1) : n = 0 := by
  have hn : n < 1 := by exact_mod_cast h
  omega

theorem terminal_count_zero (n : ℕ) (q : ℚ)
    (hq : q = n) (h : q < 1) : n = 0 := by
  apply terminal_potential_zero n
  simpa [hq] using h

def W (k n : ℕ) : Prop := k < n

theorem quantifier_firewall :
    (∀ k, ∃ n, W k n) ∧ ¬ (∃ n, ∀ k, W k n) := by
  constructor
  · exact fun k => ⟨k + 1, Nat.lt_succ_self k⟩
  · rintro ⟨n, hn⟩
    exact (Nat.lt_irrefl n) (hn n)

theorem quarter_integral (ell : ℕ) (h : 2 ≤ ell) : 4 ∣ 2 ^ ell := by
  rw [show ell = 2 + (ell - 2) by omega, pow_add]
  norm_num
end PNPCore

namespace BSDCore

theorem faithful_realization {V W : Type} (f : V → W)
    (hf : Function.Injective f) {x y : V} (h : f x = f y) : x = y := hf h

theorem unit_ambiguity : ∃ x y : ℤ, x ≠ y ∧ x * x = y * y := by
  refine ⟨1, -1, ?_, ?_⟩ <;> norm_num

noncomputable def haar (d : ℝ) := d⁻¹ ^ 2

noncomputable def jacobian (d : ℝ) := d⁻¹ ^ 4

def inverseDensity (d : ℝ) := d ^ 2

noncomputable def transformed (d : ℝ) := inverseDensity d * jacobian d

noncomputable def naivelySquared (d : ℝ) := haar d * haar d

theorem transformed_eq_haar {d : ℝ} (hd : d ≠ 0) :
    transformed d = haar d := by
  field_simp [transformed, inverseDensity, jacobian, haar, inv_pow, hd]
  ring

theorem determinant_two_mismatch : transformed 2 ≠ naivelySquared 2 := by
  norm_num [transformed, inverseDensity, jacobian, naivelySquared, haar]
end BSDCore

structure ExactPass2 : Prop where
  rhResidual : ∀ a b : ℝ, 0 ≤ RHCore.residual a b
  rhEdge : ∀ t d m n y : ℝ,
    -(2*t+d)*y + (t-m)*y + (t-n)*y = -(d+m+n)*y
  pnpSampling : ((3 : ℚ) / 4) ^ 8 < (1 : ℚ) / 8
  pnpQuantifiers : (∀ k, ∃ n, PNPCore.W k n) ∧ ¬ (∃ n, ∀ k, PNPCore.W k n)
  bsdAmbiguity : ∃ x y : ℤ, x ≠ y ∧ x*x = y*y
  bsdMismatch : BSDCore.transformed 2 ≠ BSDCore.naivelySquared 2

theorem exactPass2 : ExactPass2 := {
  rhResidual := RHCore.residual_nonneg
  rhEdge := RHCore.edge_identity
  pnpSampling := PNPCore.sampling_bound
  pnpQuantifiers := PNPCore.quantifier_firewall
  bsdAmbiguity := BSDCore.unit_ambiguity
  bsdMismatch := BSDCore.determinant_two_mismatch }

#print axioms RHCore.residual_nonneg
#print axioms RHCore.abel_floor
#print axioms RHCore.schur_residual
#print axioms PNPCore.sampling_bound
#print axioms PNPCore.eventual_majorant
#print axioms PNPCore.one_child_lt_one
#print axioms PNPCore.quantifier_firewall
#print axioms BSDCore.transformed_eq_haar
#print axioms BSDCore.determinant_two_mismatch
#print axioms exactPass2

end UnifiedPass2
end Millennium
