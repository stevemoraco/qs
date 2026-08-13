import Mathlib

/-!
Finite Fourier/Leray algebra for the first exterior return path of the
three-plane Navier--Stokes relay braid.

The file proves:
* planar passive-polarization interactions survive Leray projection exactly;
* reality-partner pump shifts have equal forward and reverse coefficients;
* the explicit braid ladder has the same nonzero coefficient in both directions;
* a one-mode Schur self-energy is at least one half of the active transfer scale
  whenever exterior damping does not exceed the coupling scale.

This is a finite algebraic firewall. It does not formalize Fourier series,
Navier--Stokes solutions, an invariant manifold, a full tail inverse, or a Clay
Millennium theorem.
-/

namespace NSBraidReturnSelfEnergy

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

@[ext]
structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

def dot (u v : V3) : ℝ := u.x * v.x + u.y * v.y + u.z * v.z

def add (u v : V3) : V3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

def sub (u v : V3) : V3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩

def smul (a : ℝ) (u : V3) : V3 := ⟨a * u.x, a * u.y, a * u.z⟩

def planar (x y : ℝ) : V3 := ⟨x, y, 0⟩

def normal : V3 := ⟨0, 0, 1⟩

def pump (ux uy uz : ℝ) : V3 := ⟨ux, uy, uz⟩

/-- Numerator of the symmetrized Euler bilinear Fourier symbol. -/
def symSymbol (k u v : V3) : V3 :=
  add (smul (dot u k) v) (smul (dot v k) u)

/-- Orthogonal projection onto the plane perpendicular to `k`. -/
noncomputable def leray (k s : V3) : V3 :=
  sub s (smul (dot s k / dot k k) k)

/-- A normal polarization is fixed exactly by Leray projection at every planar
carrier, including the algebraically harmless zero-carrier case. -/
theorem leray_planar_normal (kx ky c : ℝ) :
    leray (planar kx ky) (smul c normal) = smul c normal := by
  unfold leray
  apply V3.ext <;>
    simp [planar, normal, smul, sub, dot]

/-- For a planar output carrier, the pump/normal interaction is already normal,
so projection does not change it. -/
theorem projected_planar_passive
    (kx ky ux uy uz z : ℝ) :
    leray (planar kx ky)
      (symSymbol (planar kx ky) (pump ux uy uz) (smul z normal)) =
      smul ((ux * kx + uy * ky) * z) normal := by
  rw [show symSymbol (planar kx ky) (pump ux uy uz) (smul z normal) =
      smul ((ux * kx + uy * ky) * z) normal by
    apply V3.ext <;>
      simp [symSymbol, planar, pump, normal, add, smul, dot] <;>
      ring]
  exact leray_planar_normal kx ky ((ux * kx + uy * ky) * z)

/-- A pump transverse to its own shift has the same scalar coefficient on the
forward edge `k -> k+q` and the reverse edge `k+q -> k`. -/
theorem planar_forward_reverse_reciprocity
    (qx qy kx ky ux uy uz z : ℝ)
    (htransverse : ux * qx + uy * qy = 0) :
    leray (planar (kx + qx) (ky + qy))
      (symSymbol (planar (kx + qx) (ky + qy))
        (pump ux uy uz) (smul z normal)) =
    leray (planar kx ky)
      (symSymbol (planar kx ky)
        (pump ux uy uz) (smul z normal)) := by
  rw [projected_planar_passive, projected_planar_passive]
  have hcoef :
      ux * (kx + qx) + uy * (ky + qy) = ux * kx + uy * ky := by
    calc
      ux * (kx + qx) + uy * (ky + qy) =
          ux * kx + uy * ky + (ux * qx + uy * qy) := by ring
      _ = ux * kx + uy * ky := by rw [htransverse]; ring
  rw [hcoef]

def braidPump : V3 := ⟨-1, 0, 1⟩

def braidCarrier (N n : ℝ) : V3 := planar N (n * N)

/-- Every adjacent edge of the explicit exterior ladder has coefficient
`-B*N`, independently of the ladder index. -/
theorem braid_ladder_step (N B n z : ℝ) :
    leray (braidCarrier N n)
      (symSymbol (braidCarrier N n) (smul B braidPump) (smul z normal)) =
      smul (-B * N * z) normal := by
  rw [show smul B braidPump = pump (-B) 0 B by
    apply V3.ext <;> simp [smul, pump, braidPump]]
  simpa [braidCarrier] using
    (projected_planar_passive N (n * N) (-B) 0 B z)

/-- In particular, the active-to-exterior and exterior-to-active symbols in
the first braid ladder edge are exactly equal. -/
theorem first_braid_edge_is_reciprocal (N B z : ℝ) :
    leray (braidCarrier N 2)
      (symSymbol (braidCarrier N 2) (smul B braidPump) (smul z normal)) =
    leray (braidCarrier N 1)
      (symSymbol (braidCarrier N 1) (smul B braidPump) (smul z normal)) := by
  rw [braid_ladder_step, braid_ladder_step]

/-- Two consecutive scalar edge coefficients multiply to the square coupling;
there is no projection or scale loss in the two-step path. -/
theorem two_step_coupling_square (N B z : ℝ) :
    (-B * N) * ((-B * N) * z) = (B * N) ^ 2 * z := by
  ring

/-- The first active and exterior carriers have squared lengths `2N^2` and
`5N^2`; they are on comparable scales. -/
theorem first_braid_carrier_norms (N : ℝ) :
    dot (braidCarrier N 1) (braidCarrier N 1) = 2 * N ^ 2 ∧
    dot (braidCarrier N 2) (braidCarrier N 2) = 5 * N ^ 2 := by
  constructor <;>
    simp [dot, braidCarrier, planar] <;>
    ring

/-- Scalar one-mode return self-energy after eliminating an exterior mode with
damping `d` at Laplace parameter `lambda`. -/
noncomputable def selfEnergy (gamma d lambda : ℝ) : ℝ := gamma ^ 2 / (lambda + d)

/-- The self-energy normalized by the active coupling scale at
`lambda = gamma`. -/
noncomputable def normalizedReturn (gamma d : ℝ) : ℝ := gamma / (gamma + d)

theorem selfEnergy_at_coupling_scale
    {gamma d : ℝ} (hgamma : 0 < gamma) (hd : 0 ≤ d) :
    selfEnergy gamma d gamma / gamma = normalizedReturn gamma d := by
  have hgamma0 : gamma ≠ 0 := ne_of_gt hgamma
  have hden0 : gamma + d ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hgamma hd)
  unfold selfEnergy normalizedReturn
  field_simp [hgamma0, hden0]

/-- If exterior damping is no larger than the coupling scale, the normalized
one-path return self-energy is at least one half. -/
theorem normalizedReturn_ge_half
    {gamma d : ℝ}
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hdle : d ≤ gamma) :
    (1 : ℝ) / 2 ≤ normalizedReturn gamma d := by
  unfold normalizedReturn
  have hden : 0 < gamma + d := add_pos_of_pos_of_nonneg hgamma hd
  apply (le_div_iff₀ hden).2
  nlinarith

/-- The same normalized return is never larger than one for nonnegative
damping. -/
theorem normalizedReturn_le_one
    {gamma d : ℝ} (hgamma : 0 < gamma) (hd : 0 ≤ d) :
    normalizedReturn gamma d ≤ 1 := by
  unfold normalizedReturn
  have hden : 0 < gamma + d := add_pos_of_pos_of_nonneg hgamma hd
  apply (div_le_iff₀ hden).2
  nlinarith

/-- Conversely, making this path smaller than one half forces damping to
strictly dominate the coupling. -/
theorem normalizedReturn_lt_half_forces_damping
    {gamma d : ℝ}
    (hgamma : 0 < gamma) (hd : 0 ≤ d)
    (hsmall : normalizedReturn gamma d < (1 : ℝ) / 2) :
    gamma < d := by
  by_contra hnot
  have hdle : d ≤ gamma := le_of_not_gt hnot
  have hhalf := normalizedReturn_ge_half hgamma hd hdle
  linarith

/-- Combined Schur firewall in the transfer-dominant regime. -/
theorem selfEnergy_return_ge_half
    {gamma d : ℝ}
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hdle : d ≤ gamma) :
    (1 : ℝ) / 2 ≤ selfEnergy gamma d gamma / gamma := by
  rw [selfEnergy_at_coupling_scale hgamma hd]
  exact normalizedReturn_ge_half hgamma hd hdle

/-- Therefore no claimed uniform return budget strictly below one half can be
deduced from projection plus transfer-dominant damping for this path alone. -/
theorem no_budget_below_half
    {gamma d delta : ℝ}
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hdle : d ≤ gamma)
    (hdelta : delta < (1 : ℝ) / 2) :
    ¬ selfEnergy gamma d gamma / gamma ≤ delta := by
  intro hbudget
  have hhalf := selfEnergy_return_ge_half hgamma hd hdle
  linarith

#print axioms leray_planar_normal
#print axioms projected_planar_passive
#print axioms planar_forward_reverse_reciprocity
#print axioms braid_ladder_step
#print axioms first_braid_edge_is_reciprocal
#print axioms two_step_coupling_square
#print axioms first_braid_carrier_norms
#print axioms selfEnergy_at_coupling_scale
#print axioms normalizedReturn_ge_half
#print axioms normalizedReturn_le_one
#print axioms normalizedReturn_lt_half_forces_damping
#print axioms selfEnergy_return_ge_half
#print axioms no_budget_below_half

end NSBraidReturnSelfEnergy
