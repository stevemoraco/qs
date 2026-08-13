import Mathlib

namespace RHSuzukiSquareRootDescent

/-- One-step algebra behind the identity
`Delta(x)=I(x)-I(x^2)-2 log x`: positivity of the deficit forces a drop
when passing from `x` to `x^2`. -/
theorem positive_deficit_forces_drop
    {Ix Ix2 l d : ℝ}
    (hdef : d = Ix - Ix2 - 2 * l)
    (hd : 0 < d) :
    Ix2 < Ix - 2 * l := by
  linarith

/-- Two consecutive descent steps add their losses. -/
theorem two_drop_steps
    {I0 I1 I2 a0 a1 : ℝ}
    (h01 : I1 < I0 - a0)
    (h12 : I2 < I1 - a1) :
    I2 < I0 - (a0 + a1) := by
  linarith

/-- Three consecutive descent steps add their losses. -/
theorem three_drop_steps
    {I0 I1 I2 I3 a0 a1 a2 : ℝ}
    (h01 : I1 < I0 - a0)
    (h12 : I2 < I1 - a1)
    (h23 : I3 < I2 - a2) :
    I3 < I0 - (a0 + a1 + a2) := by
  linarith

/-- Pure asymptotic margin algebra: if the normalized primitive is `-c+e1`
at scale `x` and `-c+e2` at scale `x^2`, the normalized two-scale deficit is
`(c-2)+e1-2e2`. -/
theorem two_scale_limit_algebra
    {c e1 e2 : ℝ} :
    (-c + e1) - 2 * (-c + e2) - 2 = (c - 2) + e1 - 2 * e2 := by
  ring

/-- A strictly positive limiting margin follows from `2<c`. -/
theorem margin_positive {c : ℝ} (hc : 2 < c) : 0 < c - 2 := by
  linarith

/-- If the terminal compact-scale contribution is bounded by `C` and the
accumulated square-root descent supplies `2 log y`, then sufficiently large
`log y` forces negativity. -/
theorem compact_bound_forces_negative
    {Iy C ly : ℝ}
    (hI : Iy < C - 2 * ly)
    (hlarge : C / 2 < ly) :
    Iy < 0 := by
  linarith

#print axioms positive_deficit_forces_drop
#print axioms two_drop_steps
#print axioms three_drop_steps
#print axioms two_scale_limit_algebra
#print axioms margin_positive
#print axioms compact_bound_forces_negative

end RHSuzukiSquareRootDescent
