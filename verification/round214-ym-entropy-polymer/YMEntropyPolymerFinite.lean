import Mathlib

/-!
# Round 214 Yang--Mills entropy/polymer finite cores

This file formalizes only finite dyadic exponent identities, elementary
polymer-majorant algebra, and one finite-prefix countermodel. It does not
formalize probability measures, lattice gauge theory, heat kernels, cluster
expansions, renormalization, Osterwalder--Schrader axioms, Hamiltonians, or the
Yang--Mills mass gap.
-/

namespace Millennium
namespace Round214YangMills

/-- Dyadic number of cells in an abstract `D`-dimensional fixed physical
volume at scale `2^{-j}`. -/
def dyadicCellCount (D j : ℕ) : ℚ := (2 : ℚ) ^ (D * j)

/-- Abstract per-cell bad-event power tail `2^{-kappa j}`. -/
def dyadicBadTail (kappa j : ℕ) : ℚ := (1 / 2 : ℚ) ^ (kappa * j)

/-- A strict exponent margin `r` beyond the volume dimension leaves the exact
geometric factor `2^{-rj}` after the union-bound entropy is paid. -/
theorem dyadic_entropy_tail_margin_identity
    (D r j : ℕ) :
    dyadicCellCount D j * dyadicBadTail (D + r) j =
      dyadicBadTail r j := by
  unfold dyadicCellCount dyadicBadTail
  rw [Nat.add_mul, pow_add]
  calc
    (2 : ℚ) ^ (D * j) *
        ((1 / 2 : ℚ) ^ (D * j) * (1 / 2 : ℚ) ^ (r * j)) =
      ((2 : ℚ) ^ (D * j) * (1 / 2 : ℚ) ^ (D * j)) *
        (1 / 2 : ℚ) ^ (r * j) := by ring
    _ = ((2 : ℚ) * (1 / 2 : ℚ)) ^ (D * j) *
        (1 / 2 : ℚ) ^ (r * j) := by rw [mul_pow]
    _ = (1 / 2 : ℚ) ^ (r * j) := by norm_num

/-- At the critical exponent equal to the volume dimension, the elementary
entropy-tail product is exactly scale-independent. -/
theorem dyadic_entropy_tail_critical_balance
    (D j : ℕ) :
    dyadicCellCount D j * dyadicBadTail D j = 1 := by
  unfold dyadicCellCount dyadicBadTail
  calc
    (2 : ℚ) ^ (D * j) * (1 / 2 : ℚ) ^ (D * j) =
      ((2 : ℚ) * (1 / 2 : ℚ)) ^ (D * j) := by rw [mul_pow]
    _ = 1 := by norm_num

/-- Rooted connected-polymer growth `A^n` times a per-cell activity `q^n`
is exactly the geometric majorant `(Aq)^n`. -/
theorem rooted_polymer_majorant_factorization
    (A q : ℝ) (n : ℕ) :
    A ^ n * q ^ n = (A * q) ^ n := by
  exact (mul_pow A q n).symm

/-- The local cluster-expansion ratio is below one whenever the per-cell
activity is below the reciprocal of the rooted lattice-animal constant. -/
theorem local_polymer_ratio_below_one
    (A q : ℝ)
    (hA : 0 < A)
    (hq : q < 1 / A) :
    A * q < 1 := by
  rw [lt_div_iff₀ hA] at hq
  simpa [mul_comm] using hq

/-- Control of any fixed finite prefix of observable sectors does not imply
control of the next sector, hence cannot by itself certify a full-sector gap. -/
theorem finite_observable_prefix_not_full_sector :
    ∃ Controlled : ℕ → Prop,
      (∀ n < 3, Controlled n) ∧
      ¬ ∀ n, Controlled n := by
  refine ⟨fun n => n < 3, ?_⟩
  constructor
  · intro n hn
    exact hn
  · intro hall
    have hbad := hall 3
    omega

#print axioms dyadic_entropy_tail_margin_identity
#print axioms dyadic_entropy_tail_critical_balance
#print axioms rooted_polymer_majorant_factorization
#print axioms local_polymer_ratio_below_one
#print axioms finite_observable_prefix_not_full_sector

end Round214YangMills
end Millennium
