import Mathlib

/-!
Finite polynomial shadow of the three completed vertical cubic orders classified
in `stevemoraco/RH#571` at the Hodge endpoint `(q,a,b)=(1,7,6)`.

Formalized:
* determinant-index calculations from the three multiplication tables;
* binary-cubic discriminants `-27*u^4`, `4*u^3`, and `4*u^5`;
* the fixed-split-basis discriminant factorization when the leading cubic
  coefficient vanishes;
* the exact degree-five jet expansion and its first nonzero coefficient;
* the scalar conductor/discriminant degree ledgers.

Not formalized:
the classification of completed DVR orders, normalization/conductor length,
weighted Enriques diagrams, Stein contractions, Gorenstein singularities,
triple covers, K3 surfaces, Hodge structures, or the Hodge conjecture.
-/

namespace Millennium.Hodge.R3Q1A7VerticalLocalOrders

/-- Determinant of the columns `(1,0,0)`, `(0,p,q)`, and `(*,x,y)`. -/
def unitColumnDet {R : Type*} [CommRing R]
    (p q x y : R) : R :=
  p * y - q * x

/-- Binary-cubic discriminant in the convention
`a*Z^3+b*Z^2*W+c*Z*W^2+d*W^3`. -/
def cubicDisc {R : Type*} [CommRing R]
    (a b c d : R) : R :=
  b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d -
    27 * a ^ 2 * d ^ 2 + 18 * a * b * c * d

/-- For the totally ramified degree-three order, the square coordinates
`X^2=Y`, `XY=u^2`, `Y^2=u^2*X` give the index cubic
`p^3-u^2*q^3`. -/
theorem terminal_degree_three_index
    {R : Type*} [CommRing R] (u p q : R) :
    unitColumnDet p q (q ^ 2 * u ^ 2) (p ^ 2) =
      p ^ 3 - u ^ 2 * q ^ 3 := by
  simp [unitColumnDet]
  ring

/-- For a ramified quadratic cusp plus a separate sheet, the multiplication
coordinates give `p*(q^2-u^3*p^2)`. -/
theorem degree_two_plus_one_index
    {R : Type*} [CommRing R] (u p q : R) :
    unitColumnDet p q 0 (q ^ 2 - p ^ 2 * u ^ 3) =
      p * (q ^ 2 - u ^ 3 * p ^ 2) := by
  simp [unitColumnDet]
  ring

/-- For the square-zero non-Gorenstein `1+2` order, the multiplication
coordinates give `u*p*q^2-u^2*p^3`. -/
theorem square_zero_one_plus_two_index
    {R : Type*} [CommRing R] (u p q : R) :
    unitColumnDet p q 0 (q ^ 2 * u - p ^ 2 * u ^ 2) =
      u * p * q ^ 2 - u ^ 2 * p ^ 3 := by
  simp [unitColumnDet]
  ring

/-- Discriminant of `Z^3-u^2*W^3`. -/
theorem terminal_degree_three_discriminant
    {R : Type*} [CommRing R] (u : R) :
    cubicDisc 1 0 0 (-u ^ 2) = -27 * u ^ 4 := by
  simp [cubicDisc]

/-- Discriminant of `W*(Z^2-u^3*W^2)`. -/
theorem degree_two_plus_one_discriminant
    {R : Type*} [CommRing R] (u : R) :
    cubicDisc 0 1 0 (-u ^ 3) = 4 * u ^ 3 := by
  simp [cubicDisc]
  ring

/-- Discriminant of `u*W*(Z^2-u*W^2)`. -/
theorem square_zero_one_plus_two_discriminant
    {R : Type*} [CommRing R] (u : R) :
    cubicDisc 0 u 0 (-u ^ 2) = 4 * u ^ 5 := by
  simp [cubicDisc]
  ring

/-- If the leading coefficient vanishes, the discriminant factors as
`b^2*(c^2-4*b*d)`. -/
theorem leading_coefficient_zero_factorization
    {R : Type*} [CommRing R] (b c d : R) :
    cubicDisc 0 b c d = b ^ 2 * (c ^ 2 - 4 * b * d) := by
  simp [cubicDisc]
  ring

/-- Exact fixed-basis jet expansion for
`B=b1*v`, `C=c1*v+c2*v^2`, `D=d1*v+d2*v^2+d3*v^3`. -/
theorem square_zero_vertical_jet_expansion
    {R : Type*} [CommRing R]
    (b₁ c₁ c₂ d₁ d₂ d₃ v : R) :
    cubicDisc 0
        (b₁ * v)
        (c₁ * v + c₂ * v ^ 2)
        (d₁ * v + d₂ * v ^ 2 + d₃ * v ^ 3) =
      b₁ ^ 2 * (c₁ ^ 2 - 4 * b₁ * d₁) * v ^ 4 +
      b₁ ^ 2 * (2 * c₁ * c₂ - 4 * b₁ * d₂) * v ^ 5 +
      b₁ ^ 2 * (c₂ ^ 2 - 4 * b₁ * d₃) * v ^ 6 := by
  simp [cubicDisc]
  ring

/-- After the order-four coefficient vanishes, the first two remaining
coefficients are exactly the order-five and order-six jet coefficients. -/
theorem square_zero_vertical_jet_after_tangency
    {R : Type*} [CommRing R]
    (b₁ c₁ c₂ d₁ d₂ d₃ v : R)
    (htangent : c₁ ^ 2 = 4 * b₁ * d₁) :
    cubicDisc 0
        (b₁ * v)
        (c₁ * v + c₂ * v ^ 2)
        (d₁ * v + d₂ * v ^ 2 + d₃ * v ^ 3) =
      b₁ ^ 2 * (2 * c₁ * c₂ - 4 * b₁ * d₂) * v ^ 5 +
      b₁ ^ 2 * (c₂ ^ 2 - 4 * b₁ * d₃) * v ^ 6 := by
  rw [square_zero_vertical_jet_expansion]
  rw [htangent]
  ring

/-- Over a field, the asserted order-five coefficient is nonzero exactly when
`b1` and the second jet obstruction are nonzero. -/
theorem order_five_coefficient_nonzero
    {K : Type*} [Field K]
    (b₁ c₁ c₂ d₂ : K)
    (hb : b₁ ≠ 0)
    (hsecond : 2 * c₁ * c₂ - 4 * b₁ * d₂ ≠ 0) :
    b₁ ^ 2 * (2 * c₁ * c₂ - 4 * b₁ * d₂) ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero 2 hb) hsecond

/-- The integral degree-three normalization ledger: normalized discriminant
four plus twice delta one gives the cubic discriminant degree six. -/
theorem integral_discriminant_degree_ledger :
    (4 : ℕ) + 2 * 1 = 6 := by
  norm_num

/-- The `1+2` normalization ledger: normalized discriminant two plus twice
delta two gives the cubic discriminant degree six. -/
theorem split_discriminant_degree_ledger :
    (2 : ℕ) + 2 * 2 = 6 := by
  norm_num

/-- The three local orders contribute discriminant orders three, four, or five,
all strictly below the total vertical degree six. -/
theorem local_discriminant_orders_bounded :
    (3 : ℕ) < 6 ∧ (4 : ℕ) < 6 ∧ (5 : ℕ) < 6 := by
  norm_num

#check terminal_degree_three_index
#check degree_two_plus_one_index
#check square_zero_one_plus_two_index
#check terminal_degree_three_discriminant
#check degree_two_plus_one_discriminant
#check square_zero_one_plus_two_discriminant
#check leading_coefficient_zero_factorization
#check square_zero_vertical_jet_expansion
#check square_zero_vertical_jet_after_tangency
#check order_five_coefficient_nonzero
#check integral_discriminant_degree_ledger
#check split_discriminant_degree_ledger
#check local_discriminant_orders_bounded

#print axioms terminal_degree_three_index
#print axioms degree_two_plus_one_index
#print axioms square_zero_one_plus_two_index
#print axioms terminal_degree_three_discriminant
#print axioms degree_two_plus_one_discriminant
#print axioms square_zero_one_plus_two_discriminant
#print axioms leading_coefficient_zero_factorization
#print axioms square_zero_vertical_jet_expansion
#print axioms square_zero_vertical_jet_after_tangency
#print axioms order_five_coefficient_nonzero
#print axioms integral_discriminant_degree_ledger
#print axioms split_discriminant_degree_ledger
#print axioms local_discriminant_orders_bounded

end Millennium.Hodge.R3Q1A7VerticalLocalOrders
