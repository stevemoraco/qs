import Mathlib

/-!
Finite intersection-algebra companion to `stevemoraco/RH#572`.

This file verifies only the three explicit canonical-cycle linear systems and
proves that none has an integral solution. It does not formalize the Enriques
proximity census, K3 geometry, Stein contraction, analytic canonical cover,
Némethi theory, Miranda equations, or the Hodge conjecture.
-/

namespace HodgeBasketBSixfoldGraphFinite

/-- Type I rational canonical-cycle vector satisfies the displayed adjunction
linear system. Vertex order: `(F,E0,E1,A,B)`. -/
theorem typeI_canonical_fraction :
    let f : ℚ := 10 / 3
    let e0 : ℚ := 7 / 3
    let e1 : ℚ := 10 / 9
    let a : ℚ := 14 / 9
    let b : ℚ := 7 / 9
    (-f + e0 = -1) ∧
    (f - 3 * e0 + e1 + a = -1) ∧
    (e0 - 3 * e1 = -1) ∧
    (e0 - 2 * a + b = 0) ∧
    (a - 2 * b = 0) := by
  norm_num

/-- Type I has no integral canonical cycle: the canonical adjunction system is
inconsistent over `ℤ`. -/
theorem typeI_no_integral_canonical
    (f e0 e1 a b : ℤ)
    (hF : -f + e0 = -1)
    (h0 : f - 3 * e0 + e1 + a = -1)
    (h1 : e0 - 3 * e1 = -1)
    (hA : e0 - 2 * a + b = 0)
    (hB : a - 2 * b = 0) :
    False := by
  omega

/-- Type II rational canonical-cycle vector satisfies the displayed adjunction
linear system. Vertex order: `(F,E0,E1,A,B,C)`. -/
theorem typeII_canonical_fraction :
    let f : ℚ := 10 / 3
    let e0 : ℚ := 7 / 3
    let e1 : ℚ := 11 / 9
    let a : ℚ := 8 / 3
    let b : ℚ := 16 / 9
    let c : ℚ := 8 / 9
    (-f + e0 = -1) ∧
    (f - 3 * e0 + a = -1) ∧
    (-3 * e1 + a = -1) ∧
    (e0 + e1 - 2 * a + b = 0) ∧
    (a - 2 * b + c = 0) ∧
    (b - 2 * c = 0) := by
  norm_num

/-- Type II has no integral solution to its canonical-cycle system. -/
theorem typeII_no_integral_canonical
    (f e0 e1 a b c : ℤ)
    (hF : -f + e0 = -1)
    (h0 : f - 3 * e0 + a = -1)
    (h1 : -3 * e1 + a = -1)
    (hA : e0 + e1 - 2 * a + b = 0)
    (hB : a - 2 * b + c = 0)
    (hC : b - 2 * c = 0) :
    False := by
  omega

/-- Type III rational canonical-cycle vector satisfies the displayed adjunction
linear system. Vertex order: `(F,E0,E1,A,B,C,D)`. -/
theorem typeIII_canonical_fraction :
    let f : ℚ := 10 / 3
    let e0 : ℚ := 7 / 3
    let e1 : ℚ := 4 / 3
    let a : ℚ := 8 / 3
    let b : ℚ := 3
    let c : ℚ := 2
    let d : ℚ := 1
    (-f + e0 = -1) ∧
    (f - 3 * e0 + a = -1) ∧
    (-3 * e1 + b = -1) ∧
    (e0 - 2 * a + b = 0) ∧
    (e1 + a - 2 * b + c = 0) ∧
    (b - 2 * c + d = 0) ∧
    (c - 2 * d = 0) := by
  norm_num

/-- Type III also has no integral solution to its canonical-cycle system. -/
theorem typeIII_no_integral_canonical
    (f e0 e1 a b c d : ℤ)
    (hF : -f + e0 = -1)
    (h0 : f - 3 * e0 + a = -1)
    (h1 : -3 * e1 + b = -1)
    (hA : e0 - 2 * a + b = 0)
    (hB : e1 + a - 2 * b + c = 0)
    (hC : b - 2 * c + d = 0)
    (hD : c - 2 * d = 0) :
    False := by
  omega

#print axioms HodgeBasketBSixfoldGraphFinite.typeI_canonical_fraction
#print axioms HodgeBasketBSixfoldGraphFinite.typeI_no_integral_canonical
#print axioms HodgeBasketBSixfoldGraphFinite.typeII_canonical_fraction
#print axioms HodgeBasketBSixfoldGraphFinite.typeII_no_integral_canonical
#print axioms HodgeBasketBSixfoldGraphFinite.typeIII_canonical_fraction
#print axioms HodgeBasketBSixfoldGraphFinite.typeIII_no_integral_canonical

end HodgeBasketBSixfoldGraphFinite
