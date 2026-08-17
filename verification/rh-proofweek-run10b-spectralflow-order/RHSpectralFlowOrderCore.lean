import Mathlib

/-!
# Order-theoretic and finite-signature cores for typed Suzuki interfaces

This file formalizes elementary consequences of two abstract monotonicity inputs
and the scalar algebra of one conjugate-pair hyperbolic block.

The two Suzuki applications must not be conflated:

* an antitone real-valued spectral floor is intended for Suzuki 2026's lowest
  localized Weil/Friedrichs eigenvalue `lambda_a`;
* a monotone natural-valued negative index is intended for Suzuki 2023's bounded
  screw-kernel form `H_a` and its exact source-native Schur matrices `S_a[N]`.

The pair-block identities are only real scalar shadows of the Hermitian
`[[0,m],[m,0]]` block appearing after a finite zero truncation; they do not
formalize zero evaluation, DYL, Paley--Wiener interpolation, or the infinite
Weil tail.

The analytic domain-monotonicity proofs, the 2023 screw-form inertia identity,
the derivative bridge between compact Weil tests and the screw form, Suzuki's
operators themselves, zeta, and the Riemann Hypothesis are all external to this
file.
-/

namespace RHSpectralFlowOrderCore

theorem antitone_negative_persists
    (f : ℝ → ℝ) (hf : Antitone f)
    {a b : ℝ} (hab : a ≤ b) (ha : f a < 0) :
    f b < 0 := by
  exact lt_of_le_of_lt (hf hab) ha

theorem antitone_nonneg_of_cofinal
    (f : ℝ → ℝ) (hf : Antitone f)
    (aSeq : ℕ → ℝ)
    (hcofinal : ∀ a : ℝ, ∃ k : ℕ, a ≤ aSeq k)
    (hseq : ∀ k : ℕ, 0 ≤ f (aSeq k)) :
    ∀ a : ℝ, 0 ≤ f a := by
  intro a
  obtain ⟨k, hak⟩ := hcofinal a
  exact le_trans (hseq k) (hf hak)

theorem antitone_global_nonneg_iff_cofinal
    (f : ℝ → ℝ) (hf : Antitone f)
    (aSeq : ℕ → ℝ)
    (hcofinal : ∀ a : ℝ, ∃ k : ℕ, a ≤ aSeq k) :
    (∀ a : ℝ, 0 ≤ f a) ↔ (∀ k : ℕ, 0 ≤ f (aSeq k)) := by
  constructor
  · intro h k
    exact h (aSeq k)
  · intro h
    exact antitone_nonneg_of_cofinal f hf aSeq hcofinal h

theorem monotone_nat_zero_of_cofinal
    (idx : ℝ → ℕ) (hidx : Monotone idx)
    (aSeq : ℕ → ℝ)
    (hcofinal : ∀ a : ℝ, ∃ k : ℕ, a ≤ aSeq k)
    (hzero : ∀ k : ℕ, idx (aSeq k) = 0) :
    ∀ a : ℝ, idx a = 0 := by
  intro a
  obtain ⟨k, hak⟩ := hcofinal a
  have hle : idx a ≤ idx (aSeq k) := hidx hak
  rw [hzero k] at hle
  exact Nat.eq_zero_of_le_zero hle

theorem monotone_nat_global_zero_iff_cofinal
    (idx : ℝ → ℕ) (hidx : Monotone idx)
    (aSeq : ℕ → ℝ)
    (hcofinal : ∀ a : ℝ, ∃ k : ℕ, a ≤ aSeq k) :
    (∀ a : ℝ, idx a = 0) ↔ (∀ k : ℕ, idx (aSeq k) = 0) := by
  constructor
  · intro h k
    exact h (aSeq k)
  · intro h
    exact monotone_nat_zero_of_cofinal idx hidx aSeq hcofinal h

theorem hyperbolic_pair_hadamard
    (m x y : ℝ) :
    2 * m * x * y
      = (m / 2) * (x + y)^2 - (m / 2) * (x - y)^2 := by
  ring

theorem hyperbolic_pair_negative_direction
    (m x : ℝ) (hm : 0 < m) (hx : x ≠ 0) :
    2 * m * x * (-x) < 0 := by
  have hx2 : 0 < x^2 := sq_pos_of_ne_zero hx
  nlinarith

theorem scalar_tail_reserve_keeps_negative
    (m tail : ℝ) (h : tail < m) :
    -m + tail < 0 := by
  linarith

#print axioms antitone_negative_persists
#print axioms antitone_nonneg_of_cofinal
#print axioms antitone_global_nonneg_iff_cofinal
#print axioms monotone_nat_zero_of_cofinal
#print axioms monotone_nat_global_zero_iff_cofinal
#print axioms hyperbolic_pair_hadamard
#print axioms hyperbolic_pair_negative_direction
#print axioms scalar_tail_reserve_keeps_negative

end RHSpectralFlowOrderCore
