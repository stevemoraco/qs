import Mathlib

/-!
# SU(2) one-plaquette polynomial-closure obstruction: finite cores

Honesty status: this file formalizes only polynomial and finite-set cores. It
does not formalize SU(2), a lattice gauge measure, a Langevin process, a
Dyson--Schwinger identity, or the Yang--Mills Millennium statement.
-/

open Polynomial

namespace MillenniumBraid
namespace YMSU2PolynomialClosure

/-- The degree-raising part of the SU(2) Wilson radial drift. -/
noncomputable def degreeRaisingDrift (κ : ℝ) (p : ℝ[X]) : ℝ[X] :=
  -C κ * X ^ 2 * derivative p

/-- On a positive-degree monomial, the Wilson drift has an explicit nonzero
    term two powers above the derivative. -/
theorem degreeRaisingDrift_X_pow_succ (κ : ℝ) (n : ℕ) :
    degreeRaisingDrift κ (X ^ (n + 1)) =
      -C (κ * (n + 1 : ℝ)) * X ^ 2 * X ^ n := by
  simp [degreeRaisingDrift, derivative_X_pow_succ]
  ring

/-- No finite set of polynomial degrees can contain a positive degree and be
    closed under the successor operation. -/
theorem finite_successor_closed_degrees_are_zero
    (S : Finset ℕ)
    (hclosed : ∀ n, n ∈ S → 0 < n → n + 1 ∈ S) :
    ∀ n ∈ S, n = 0 := by
  intro n hn
  by_contra hn0
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  let hs : S.Nonempty := ⟨n, hn⟩
  let M : ℕ := S.max' hs
  have hMmem : M ∈ S := by
    exact S.max'_mem hs
  have hnleM : n ≤ M := by
    exact S.le_max' n hn
  have hMpos : 0 < M := lt_of_lt_of_le hnpos hnleM
  have hsucc : M + 1 ∈ S := hclosed M hMmem hMpos
  have hle : M + 1 ≤ M := by
    exact S.le_max' (M + 1) hsucc
  omega

/-- A nonzero coupling makes the displayed leading scalar coefficient nonzero. -/
theorem degree_raising_coefficient_ne_zero
    (κ : ℝ) (n : ℕ) (hκ : κ ≠ 0) :
    -(κ * (n + 1 : ℝ)) ≠ 0 := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  exact neg_ne_zero.mpr (mul_ne_zero hκ hn)

#print axioms degreeRaisingDrift_X_pow_succ
#print axioms finite_successor_closed_degrees_are_zero
#print axioms degree_raising_coefficient_ne_zero

end YMSU2PolynomialClosure
end MillenniumBraid
