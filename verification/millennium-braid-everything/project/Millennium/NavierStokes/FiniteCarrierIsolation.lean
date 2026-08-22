import Mathlib

/-!
# Navier--Stokes: finite high-shell carrier isolation

For finitely many packet/triad blocks, choose carrier coordinates

  K_i = K + i L.

If the gap `L` exceeds the entire low-frequency bandwidth `B`, distinct blocks
have disjoint `B`-neighbourhoods in the carrier coordinate.  If `m L <= K`, all
`m` carriers remain inside the single dyadic shell `[K,2K]`.

This is the finite arithmetic needed to prevent cross-block high-high products
from falling into a prescribed low-frequency projection.  It does not formalize
vector Fourier support, Leray projection, packets, Navier--Stokes, or blow-up.
-/

namespace Millennium.NavierStokes.FiniteCarrierIsolation

/-- Arithmetic progression of high carrier coordinates. -/
def carrier {m : ℕ} (K L : ℕ) (i : Fin m) : ℕ :=
  K + i.val * L

/-- Distinct carrier blocks are separated by at least one full gap `L`. -/
theorem carrier_gap
    {m K L : ℕ} (hL : 0 < L) {i j : Fin m} (hij : i ≠ j) :
    carrier K L i + L ≤ carrier K L j ∨
    carrier K L j + L ≤ carrier K L i := by
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · left
    have hsucc : i.val + 1 ≤ j.val := Nat.succ_le_iff.mpr hijlt
    have hmul : (i.val + 1) * L ≤ j.val * L :=
      Nat.mul_le_mul_right L hsucc
    have hmul' : i.val * L + L ≤ j.val * L := by
      simpa [Nat.add_mul] using hmul
    unfold carrier
    omega
  · right
    have hsucc : j.val + 1 ≤ i.val := Nat.succ_le_iff.mpr hjilt
    have hmul : (j.val + 1) * L ≤ i.val * L :=
      Nat.mul_le_mul_right L hsucc
    have hmul' : j.val * L + L ≤ i.val * L := by
      simpa [Nat.add_mul] using hmul
    unfold carrier
    omega

/-- If the carrier gap exceeds bandwidth `B`, distinct carrier coordinates have
strictly disjoint `B`-neighbourhoods. -/
theorem carrier_lowBands_disjoint
    {m K L B : ℕ} (hL : 0 < L) (hBL : B < L)
    {i j : Fin m} (hij : i ≠ j) :
    carrier K L i + B < carrier K L j ∨
    carrier K L j + B < carrier K L i := by
  rcases carrier_gap hL hij with h | h
  · left
    omega
  · right
    omega

/-- Every carrier lies above the shell base. -/
theorem carrier_lower_shell
    {m K L : ℕ} (i : Fin m) :
    K ≤ carrier K L i := by
  unfold carrier
  omega

/-- If the full finite progression fits in the shell budget, every carrier lies
below `2K`. -/
theorem carrier_upper_shell
    {m K L : ℕ} (hfit : m * L ≤ K) (i : Fin m) :
    carrier K L i ≤ 2 * K := by
  have hi : i.val ≤ m := Nat.le_of_lt i.isLt
  have hmul : i.val * L ≤ m * L := Nat.mul_le_mul_right L hi
  have hIK : i.val * L ≤ K := hmul.trans hfit
  unfold carrier
  omega

/-- Complete finite packing certificate: all carriers remain in `[K,2K]` and
all distinct low bands are disjoint. -/
theorem finite_shell_isolation_certificate
    {m K L B : ℕ}
    (hL : 0 < L) (hBL : B < L) (hfit : m * L ≤ K) :
    (∀ i : Fin m, K ≤ carrier K L i ∧ carrier K L i ≤ 2 * K) ∧
    (∀ i j : Fin m, i ≠ j →
      carrier K L i + B < carrier K L j ∨
      carrier K L j + B < carrier K L i) := by
  constructor
  · intro i
    exact ⟨carrier_lower_shell i, carrier_upper_shell hfit i⟩
  · intro i j hij
    exact carrier_lowBands_disjoint hL hBL hij

/-- The nine-direction stress construction needs only nine blocks; any gap and
bandwidth fit once `9L <= K`. -/
theorem nine_block_isolation
    {K L B : ℕ}
    (hL : 0 < L) (hBL : B < L) (hfit : 9 * L ≤ K) :
    (∀ i : Fin 9, K ≤ carrier K L i ∧ carrier K L i ≤ 2 * K) ∧
    (∀ i j : Fin 9, i ≠ j →
      carrier K L i + B < carrier K L j ∨
      carrier K L j + B < carrier K L i) := by
  exact finite_shell_isolation_certificate hL hBL hfit

#print axioms carrier_gap
#print axioms carrier_lowBands_disjoint
#print axioms carrier_lower_shell
#print axioms carrier_upper_shell
#print axioms finite_shell_isolation_certificate
#print axioms nine_block_isolation

end Millennium.NavierStokes.FiniteCarrierIsolation
