import Mathlib

/-!
# Finite algebra for the AO ring radial phase-current cancellation

This file formalizes only exact real-coordinate algebra used in the companion
Navier--Stokes vortex-column audit.  It does not formalize cylindrical vector
calculus, Leray projection, the Albritton--Ożański eigenvalue problem, Weber
asymptotics, Navier--Stokes, or a Clay Millennium statement.
-/

namespace NSAORingPhaseCurrent

/-- Real-coordinate form of `Im (conj u * u')` for
`u = x + i y` and `u' = xr + i yr`. -/
def phaseCurrent (x y xr yr : ℝ) : ℝ :=
  x * yr - y * xr

/-- Real part of the exact transverse-polarization defect
`-i (r u' + u) / n`. -/
def defectRe (n r x y xr yr : ℝ) : ℝ :=
  (r * yr + y) / n

/-- Imaginary part of the exact transverse-polarization defect
`-i (r u' + u) / n`. -/
def defectIm (n r x y xr yr : ℝ) : ℝ :=
  -(r * xr + x) / n

/-- Normalized zero-phase stress pairing between `u` and the exact transverse
polarization defect. -/
def stressMismatch (n r x y xr yr : ℝ) : ℝ :=
  x * defectRe n r x y xr yr + y * defectIm n r x y xr yr

/-- The pressure-correction denominators cancel exactly in
`u_theta - beta*r*u_z`.  This is the scalar coefficient identity behind
`-i(r u' + u)/n`. -/
theorem pressure_correction_denominator_cancels
    {n r beta : ℝ}
    (hn : n ≠ 0) :
    -r / (n * (1 + beta ^ 2 * r ^ 2))
      - beta * r * (beta * r ^ 2 / (n * (1 + beta ^ 2 * r ^ 2)))
      = -r / n := by
  have hden : 1 + beta ^ 2 * r ^ 2 ≠ 0 := by
    have hs : 0 ≤ (beta * r) ^ 2 := sq_nonneg (beta * r)
    nlinarith [show beta ^ 2 * r ^ 2 = (beta * r) ^ 2 by ring]
  field_simp [hn, hden]
  ring

/-- Exact Reynolds-stress mismatch: only the radial phase current survives.
The envelope-amplitude derivative cancels from the real phase average. -/
theorem stressMismatch_eq_phaseCurrent
    {n r x y xr yr : ℝ}
    (hn : n ≠ 0) :
    stressMismatch n r x y xr yr =
      (r / n) * phaseCurrent x y xr yr := by
  unfold stressMismatch defectRe defectIm phaseCurrent
  field_simp [hn]
  ring

/-- A radial derivative decomposed into real growth plus phase twist has phase
current equal to `twist * |u|^2`. -/
theorem phaseCurrent_of_growth_twist
    (x y growth twist : ℝ) :
    phaseCurrent x y
        (growth * x - twist * y)
        (growth * y + twist * x)
      = twist * (x ^ 2 + y ^ 2) := by
  unfold phaseCurrent
  ring

/-- Consequently the transverse stress defect sees phase twist, not radial
amplitude growth. -/
theorem stressMismatch_of_growth_twist
    {n r x y growth twist : ℝ}
    (hn : n ≠ 0) :
    stressMismatch n r x y
        (growth * x - twist * y)
        (growth * y + twist * x)
      = (r * twist / n) * (x ^ 2 + y ^ 2) := by
  rw [stressMismatch_eq_phaseCurrent hn,
    phaseCurrent_of_growth_twist]
  ring

/-- Constant radial phase (`twist = 0`) gives exact zero stress mismatch even
when the real radial growth is arbitrarily large. -/
theorem constant_phase_stressMismatch_zero
    {n r x y growth : ℝ}
    (hn : n ≠ 0) :
    stressMismatch n r x y (growth * x) (growth * y) = 0 := by
  simpa using
    (stressMismatch_of_growth_twist
      (n := n) (r := r) (x := x) (y := y)
      (growth := growth) (twist := 0) hn)

/-- Cylindrical Doppler forcing built from the `rz` stress and the `r theta`
stress.  The derivative arguments are supplied explicitly so this remains a
finite algebra theorem. -/
def dopplerForce
    (r beta rz drz rtheta drtheta : ℝ) : ℝ :=
  beta * (drz + rz / r) - (drtheta + 2 * rtheta / r) / r

/-- If `rtheta = beta*r*rz + q`, the derivative-enhanced leading envelope
terms cancel and only the curvature term plus the mismatch `q` remain. -/
theorem dopplerForce_mismatch_decomposition
    {r beta rz drz q dq : ℝ}
    (hr : r ≠ 0) :
    dopplerForce r beta rz drz
        (beta * r * rz + q)
        (beta * rz + beta * r * drz + dq)
      = -2 * beta * rz / r - dq / r - 2 * q / r ^ 2 := by
  unfold dopplerForce
  field_simp [hr]
  ring

/-- Substituting `q = r*j/n` reduces the complete derivative-enhanced defect to
`-j'/n - 3j/(nr)`. -/
theorem dopplerForce_phaseCurrent_decomposition
    {n r beta rz drz j dj : ℝ}
    (hn : n ≠ 0)
    (hr : r ≠ 0) :
    dopplerForce r beta rz drz
        (beta * r * rz + r * j / n)
        (beta * rz + beta * r * drz + (j + r * dj) / n)
      = -2 * beta * rz / r - dj / n - 3 * j / (n * r) := by
  unfold dopplerForce
  field_simp [hn, hr]
  ring

/-- If the phase current and its radial derivative vanish, only the cylindrical
curvature remainder survives. -/
theorem zero_phaseCurrent_dopplerForce
    {n r beta rz drz : ℝ}
    (hn : n ≠ 0)
    (hr : r ≠ 0) :
    dopplerForce r beta rz drz
        (beta * r * rz + r * 0 / n)
        (beta * rz + beta * r * drz + (0 + r * 0) / n)
      = -2 * beta * rz / r := by
  simpa using
    (dopplerForce_phaseCurrent_decomposition
      (n := n) (r := r) (beta := beta) (rz := rz) (drz := drz)
      (j := 0) (dj := 0) hn hr)

#print axioms pressure_correction_denominator_cancels
#print axioms stressMismatch_eq_phaseCurrent
#print axioms phaseCurrent_of_growth_twist
#print axioms stressMismatch_of_growth_twist
#print axioms constant_phase_stressMismatch_zero
#print axioms dopplerForce_mismatch_decomposition
#print axioms dopplerForce_phaseCurrent_decomposition
#print axioms zero_phaseCurrent_dopplerForce

end NSAORingPhaseCurrent
