import Mathlib

namespace Millennium.Hodge.LocalAtiyahSquare

/-- Coefficients of a one-form in the ordered basis `du,dv,dw,dz`. -/
structure OneForm4 where
  u : ℤ
  v : ℤ
  w : ℤ
  z : ℤ
  deriving DecidableEq

/-- Coefficients of a two-form in the ordered basis
`du∧dv, du∧dw, du∧dz, dv∧dw, dv∧dz, dw∧dz`. -/
structure TwoForm4 where
  uv : ℤ
  uw : ℤ
  uz : ℤ
  vw : ℤ
  vz : ℤ
  wz : ℤ
  deriving DecidableEq

/-- Exterior product of two symbolic one-forms. -/
def wedge (a b : OneForm4) : TwoForm4 where
  uv := a.u * b.v - a.v * b.u
  uw := a.u * b.w - a.w * b.u
  uz := a.u * b.z - a.z * b.u
  vw := a.v * b.w - a.w * b.v
  vz := a.v * b.z - a.z * b.v
  wz := a.w * b.z - a.z * b.w

def addTwo (a b : TwoForm4) : TwoForm4 where
  uv := a.uv + b.uv
  uw := a.uw + b.uw
  uz := a.uz + b.uz
  vw := a.vw + b.vw
  vz := a.vz + b.vz
  wz := a.wz + b.wz

def negOne (a : OneForm4) : OneForm4 where
  u := -a.u
  v := -a.v
  w := -a.w
  z := -a.z

def negTwo (a : TwoForm4) : TwoForm4 where
  uv := -a.uv
  uw := -a.uw
  uz := -a.uz
  vw := -a.vw
  vz := -a.vz
  wz := -a.wz

def scaleTwo (n : ℤ) (a : TwoForm4) : TwoForm4 where
  uv := n * a.uv
  uw := n * a.uw
  uz := n * a.uz
  vw := n * a.vw
  vz := n * a.vz
  wz := n * a.wz

def du : OneForm4 := ⟨1, 0, 0, 0⟩
def dv : OneForm4 := ⟨0, 1, 0, 0⟩
def dw : OneForm4 := ⟨0, 0, 1, 0⟩
def dz : OneForm4 := ⟨0, 0, 0, 1⟩

/-- The two columns of `dD₁ ∧ dD₀` for
`D₀ = [[-v,0],[u,0],[0,-z],[0,w]]` and `D₁ = [-u,-v,w,z]`. -/
def rawAtiyahSquareRow : TwoForm4 × TwoForm4 :=
  (addTwo (wedge (negOne du) (negOne dv)) (wedge (negOne dv) du),
   addTwo (wedge dw (negOne dz)) (wedge dz dw))

/-- The row after the conventional factor `1/2`. -/
def normalizedAtiyahSquareRow : TwoForm4 × TwoForm4 :=
  (wedge du dv, negTwo (wedge dw dz))

/-- BANKER: the raw matrix product is exactly twice the normalized row. -/
theorem banker_raw_square_is_twice_normalized :
    rawAtiyahSquareRow =
      (scaleTwo 2 normalizedAtiyahSquareRow.1,
       scaleTwo 2 normalizedAtiyahSquareRow.2) := by
  decide

/-- CRITIC: omitting the factor `1/2` changes the integral coefficient row. -/
theorem critic_raw_square_is_not_normalized :
    rawAtiyahSquareRow ≠ normalizedAtiyahSquareRow := by
  decide

/-- Contraction by the symbolic bivector `∂u∧∂v`. -/
def contractUV (row : TwoForm4 × TwoForm4) : ℤ × ℤ :=
  (row.1.uv, row.2.uv)

/-- CLEANER: after the exact normalization, the `uv` contraction is `(1,0)`. -/
theorem cleaner_normalized_uv_contraction :
    contractUV normalizedAtiyahSquareRow = (1, 0) := by
  decide

#print axioms banker_raw_square_is_twice_normalized
#print axioms critic_raw_square_is_not_normalized
#print axioms cleaner_normalized_uv_contraction

end Millennium.Hodge.LocalAtiyahSquare
