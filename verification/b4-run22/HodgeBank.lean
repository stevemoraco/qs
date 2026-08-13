import Mathlib

/-!
# Hodge lane: separated-node local finite core

Let
`R = ℤ[u,v,w,z]`.  This file isolates the scalar form of the local
tensor-Koszul matrices

```
D0 = [ -v   0 ]
     [  u   0 ]
     [  0  -z ]
     [  0   w ]

D1 = [ -u  -v   w   z ].
```

It proves the two entries of `D1 * D0` vanish.  It then expands a general
row of the form `D1 * hminus + hzero * D0`.  Evaluation at
`u = v = w = z = 0` sends every such row to `(0,0)`, whereas it sends
the constant row `(1,0)` to `(1,0)`.  Hence that constant row is not a
boundary of the displayed form.

This is only a finite commutative-algebra certificate.  It does not formalize
derived categories, Hochschild cohomology, semiregularity, abelian varieties,
or the Hodge conjecture.
-/

namespace Millennium.Hodge.SeparatedNodeLocalCore

abbrev Var := Fin 4
abbrev Poly := MvPolynomial Var ℤ

def u : Poly := MvPolynomial.X 0
def v : Poly := MvPolynomial.X 1
def w : Poly := MvPolynomial.X 2
def z : Poly := MvPolynomial.X 3

/-- Evaluation at the origin.  For a multivariate polynomial this is its
constant coefficient. -/
def evalZero : Poly →+* ℤ := MvPolynomial.constantCoeff

@[simp] theorem evalZero_u : evalZero u = 0 := by
  simp [evalZero, u]

@[simp] theorem evalZero_v : evalZero v = 0 := by
  simp [evalZero, v]

@[simp] theorem evalZero_w : evalZero w = 0 := by
  simp [evalZero, w]

@[simp] theorem evalZero_z : evalZero z = 0 := by
  simp [evalZero, z]

/-- First column of `D1 * D0`. -/
theorem d_one_mul_d_zero_first :
    (-u) * (-v) + (-v) * u + w * 0 + z * 0 = 0 := by
  ring

/-- Second column of `D1 * D0`. -/
theorem d_one_mul_d_zero_second :
    (-u) * 0 + (-v) * 0 + w * (-z) + z * w = 0 := by
  ring

/-- Scalar certificate for `D1 * D0 = 0`: these are exactly its two
entries. -/
theorem d_one_mul_d_zero :
    ((-u) * (-v) + (-v) * u + w * 0 + z * 0 = 0) ∧
    ((-u) * 0 + (-v) * 0 + w * (-z) + z * w = 0) :=
  ⟨d_one_mul_d_zero_first, d_one_mul_d_zero_second⟩

/-- A general `4 × 2` polynomial matrix `hminus`, stored by entries. -/
structure HMinus where
  m11 : Poly
  m12 : Poly
  m21 : Poly
  m22 : Poly
  m31 : Poly
  m32 : Poly
  m41 : Poly
  m42 : Poly

/-- A general `1 × 4` polynomial matrix `hzero`, stored by entries. -/
structure HZero where
  m1 : Poly
  m2 : Poly
  m3 : Poly
  m4 : Poly

/-- The two scalar entries of `D1 * hminus + hzero * D0`. -/
def boundaryRow (hminus : HMinus) (hzero : HZero) : Poly × Poly :=
  ( (-u) * hminus.m11 + (-v) * hminus.m21 +
      w * hminus.m31 + z * hminus.m41 +
      hzero.m1 * (-v) + hzero.m2 * u,
    (-u) * hminus.m12 + (-v) * hminus.m22 +
      w * hminus.m32 + z * hminus.m42 +
      hzero.m3 * (-z) + hzero.m4 * w )

/-- The first entry of every boundary row vanishes at the origin. -/
theorem evalZero_boundaryRow_first (hminus : HMinus) (hzero : HZero) :
    evalZero (boundaryRow hminus hzero).1 = 0 := by
  simp [boundaryRow, evalZero, u, v, w, z]

/-- The second entry of every boundary row vanishes at the origin. -/
theorem evalZero_boundaryRow_second (hminus : HMinus) (hzero : HZero) :
    evalZero (boundaryRow hminus hzero).2 = 0 := by
  simp [boundaryRow, evalZero, u, v, w, z]

/-- Evaluation at the origin sends every boundary row to `(0,0)`. -/
theorem evalZero_boundaryRow (hminus : HMinus) (hzero : HZero) :
    (evalZero (boundaryRow hminus hzero).1,
      evalZero (boundaryRow hminus hzero).2) = (0, 0) := by
  rw [evalZero_boundaryRow_first hminus hzero,
    evalZero_boundaryRow_second hminus hzero]

/-- The constant row `(1,0)` is not a row of the form
`D1 * hminus + hzero * D0`. -/
theorem constantRow_not_boundary (hminus : HMinus) (hzero : HZero) :
    boundaryRow hminus hzero ≠ ((1 : Poly), 0) := by
  intro h
  have hfirst :
      evalZero (boundaryRow hminus hzero).1 = evalZero (1 : Poly) :=
    congrArg (fun row : Poly × Poly => evalZero row.1) h
  have hzero_one : (0 : ℤ) = 1 := by
    calc
      0 = evalZero (boundaryRow hminus hzero).1 :=
        (evalZero_boundaryRow_first hminus hzero).symm
      _ = evalZero (1 : Poly) := hfirst
      _ = 1 := map_one evalZero
  exact zero_ne_one hzero_one

/-- Existential form of the augmentation certificate: no polynomial
homotopy data represents the constant row `(1,0)`. -/
theorem no_homotopy_for_constantRow :
    ¬ ∃ hminus : HMinus, ∃ hzero : HZero,
      boundaryRow hminus hzero = ((1 : Poly), 0) := by
  rintro ⟨hminus, hzero, hboundary⟩
  exact constantRow_not_boundary hminus hzero hboundary

#print axioms evalZero_u
#print axioms evalZero_v
#print axioms evalZero_w
#print axioms evalZero_z
#print axioms d_one_mul_d_zero_first
#print axioms d_one_mul_d_zero_second
#print axioms d_one_mul_d_zero
#print axioms evalZero_boundaryRow_first
#print axioms evalZero_boundaryRow_second
#print axioms evalZero_boundaryRow
#print axioms constantRow_not_boundary
#print axioms no_homotopy_for_constantRow

end Millennium.Hodge.SeparatedNodeLocalCore
