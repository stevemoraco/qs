import Mathlib

namespace HodgeQ1A8BasketAIndex5FiniteCore

/-!
Finite arithmetic shadow of the q=1,a=8 basket-A root graph reduction.

Not formalized here: proximity geometry, the resolved-pencil interpretation of
`rho`, Stein contraction, singularity Gorensteinness, K3 geometry, algebraic
cycles, or the Hodge conjecture.
-/

/-- Proximity excess along the forced 2 -> 2 -> 2 -> 2 chain. -/
theorem rho_chain_2222 :
    (2 - 2 : ℕ) = 0 ∧
    (2 - 2 : ℕ) = 0 ∧
    (2 - 2 : ℕ) = 0 ∧
    (2 : ℕ) = 2 := by
  omega

/-- Continuants of the negative length-four all-(-2) chain have absolute
values 1,2,3,4,5; in particular the determinant has absolute value five. -/
theorem minus_two_chain_continuants :
    let d0 : ℤ := 1
    let d1 : ℤ := 2
    let d2 : ℤ := 2*d1 - d0
    let d3 : ℤ := 2*d2 - d1
    let d4 : ℤ := 2*d3 - d2
    d0 = 1 ∧ d1 = 2 ∧ d2 = 3 ∧ d3 = 4 ∧ d4 = 5 := by
  norm_num

/-- The all-ones fundamental-cycle candidate is anti-nef on the chain:
end intersections are -1 and interior intersections are zero. -/
theorem all_ones_antinef_intersections :
    (-2 + 1 : ℤ) = -1 ∧
    (1 - 2 + 1 : ℤ) = 0 ∧
    (1 - 2 + 1 : ℤ) = 0 ∧
    (1 - 2 : ℤ) = -1 := by
  norm_num

/-- Exact canonical-cycle rational solution for
F(-2,g=1)--(-2)--(-2)--(-2).
The right hand side is (-K.F,0,0,0)=(-2,0,0,0). -/
theorem canonical_vector_fractions :
    let kF : ℚ := 8/5
    let k0 : ℚ := 6/5
    let k1 : ℚ := 4/5
    let k2 : ℚ := 2/5
    (-2*kF + k0 = -2) ∧
    (kF - 2*k0 + k1 = 0) ∧
    (k0 - 2*k1 + k2 = 0) ∧
    (k1 - 2*k2 = 0) := by
  norm_num

/-- The first canonical coefficient 8/5 is not integral, giving the finite
numerical-Gorenstein obstruction once the geometric canonical-cycle
identification is supplied. -/
theorem canonical_first_coefficient_not_integer :
    ¬ ∃ z : ℤ, (z : ℚ) = 8/5 := by
  intro h
  rcases h with ⟨z, hz⟩
  have hz5 : (5 : ℚ) * z = 8 := by
    rw [hz]
    norm_num
  have hzint : (5 : ℤ) * z = 8 := by
    exact_mod_cast hz5
  omega

/-- Fundamental-cycle arithmetic-genus numerator:
Z^2=-2 and K.Z=2, hence 2 + Z^2 + K.Z = 2, i.e. p_a=1. -/
theorem fundamental_genus_ledger :
    let zsq : ℤ := -2
    let kz : ℤ := 2
    2 + zsq + kz = 2 := by
  norm_num

#print axioms rho_chain_2222
#print axioms minus_two_chain_continuants
#print axioms all_ones_antinef_intersections
#print axioms canonical_vector_fractions
#print axioms canonical_first_coefficient_not_integer
#print axioms fundamental_genus_ledger

end HodgeQ1A8BasketAIndex5FiniteCore
