import Mathlib

/-!
Finite algebraic core of a selective Euler/Leray interaction.

This file proves only exact vector and polynomial identities.  It does not
construct a Navier--Stokes solution, a recursively closed packet family, or a
Clay-problem blow-up solution.
-/

namespace NSSelectiveLerayAtom

noncomputable section

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

@[ext]
structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

def dot (u v : V3) : ℝ := u.x * v.x + u.y * v.y + u.z * v.z

def add (u v : V3) : V3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

def sub (u v : V3) : V3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩

def smul (a : ℝ) (u : V3) : V3 := ⟨a * u.x, a * u.y, a * u.z⟩

def zero : V3 := ⟨0, 0, 0⟩

/-- Numerator of the symmetrized Euler bilinear Fourier symbol. -/
def symSymbol (k u v : V3) : V3 :=
  add (smul (dot u k) v) (smul (dot v k) u)

/-- Orthogonal projection onto the plane perpendicular to `k`. -/
def leray (k s : V3) : V3 :=
  sub s (smul (dot s k / dot k k) k)

def p (A H : ℝ) : V3 := ⟨A, 0, H⟩
def q (A H : ℝ) : V3 := ⟨-A, 0, H⟩
def u (A H : ℝ) : V3 := ⟨H, H, -A⟩
def v (A H : ℝ) : V3 := ⟨H, H, A⟩
def kHigh (A H : ℝ) : V3 := add (p A H) (q A H)
def kLow (A H : ℝ) : V3 := sub (p A H) (q A H)

/-- Both polarizations are exactly divergence-free at their carrier modes. -/
theorem carrier_transverse (A H : ℝ) :
    dot (p A H) (u A H) = 0 ∧ dot (q A H) (v A H) = 0 := by
  constructor <;> simp [dot, p, q, u, v] <;> ring

/-- The two carriers and the two polarizations have equal squared norms. -/
theorem equal_shell_and_norm (A H : ℝ) :
    dot (p A H) (p A H) = dot (q A H) (q A H) ∧
    dot (u A H) (u A H) = dot (v A H) (v A H) := by
  constructor <;> simp [dot, p, q, u, v] <;> ring

/-- The high-sum symbol is exactly longitudinal. -/
theorem high_symbol_parallel (A H : ℝ) :
    symSymbol (kHigh A H) (u A H) (v A H) =
      smul (-2 * A ^ 2) (kHigh A H) := by
  ext <;> simp [symSymbol, kHigh, add, smul, dot, p, q, u, v] <;> ring

/-- Therefore the high-sum symbol is annihilated exactly by Leray projection. -/
theorem high_leray_zero (A H : ℝ) :
    leray (kHigh A H) (symSymbol (kHigh A H) (u A H) (v A H)) = zero := by
  rw [high_symbol_parallel]
  unfold leray
  apply V3.ext <;>
    simp [kHigh, add, sub, smul, dot, p, q, zero] <;>
    field_simp <;>
    ring

/-- The low-difference symbol before projection. -/
theorem low_symbol_exact (A H : ℝ) :
    symSymbol (kLow A H) (u A H) (v A H) =
      ⟨4 * A * H ^ 2, 4 * A * H ^ 2, 0⟩ := by
  ext <;> simp [symSymbol, kLow, sub, add, smul, dot, p, q, u, v] <;> ring

/-- The same atom retains a transverse derivative-scale low output. -/
theorem low_leray_exact (A H : ℝ) :
    leray (kLow A H) (symSymbol (kLow A H) (u A H) (v A H)) =
      ⟨0, 4 * A * H ^ 2, 0⟩ := by
  rw [low_symbol_exact]
  unfold leray
  apply V3.ext <;>
    simp [kLow, sub, smul, dot, p, q] <;>
    field_simp <;>
    ring

/-- Exact normalized-coefficient defect identity; the correction is cubic in
`A` divided by the polarization norm squared. -/
theorem normalized_coefficient_identity (A H : ℝ)
    (hden : 2 * H ^ 2 + A ^ 2 ≠ 0) :
    2 * A * H ^ 2 / (2 * H ^ 2 + A ^ 2) =
      A - A ^ 3 / (2 * H ^ 2 + A ^ 2) := by
  field_simp
  ring

/-- The four coefficients `(1,-3,3,-1)` annihilate every sampled quadratic
of the form used by the two-point block code. -/
theorem quadratic_moment_code (H D : ℝ) :
    (2 * H + 1) ^ 2
      - 3 * (2 * H + 2 * D + 1) ^ 2
      + 3 * (2 * H + 4 * D + 1) ^ 2
      - (2 * H + 6 * D + 1) ^ 2 = 0 := by
  ring

/-! An explicit integer witness shows why distinct selective frames do not
superpose for free: each intended low survives, but their cross interaction
occupies a nonzero transverse Fourier fiber. -/

def p₁ : V3 := ⟨1, 0, -1⟩
def q₁ : V3 := ⟨-1, 0, -1⟩
def u₁ : V3 := ⟨-1, 1, -1⟩
def v₁ : V3 := ⟨-1, 1, 1⟩

def p₂ : V3 := ⟨1, 1, 0⟩
def q₂ : V3 := ⟨-1, 1, 0⟩
def u₂ : V3 := ⟨-1, 1, 1⟩
def v₂ : V3 := ⟨-1, -1, 1⟩

theorem two_frame_carrier_transverse :
    dot p₁ u₁ = 0 ∧ dot q₁ v₁ = 0 ∧
    dot p₂ u₂ = 0 ∧ dot q₂ v₂ = 0 := by
  norm_num [dot, p₁, q₁, u₁, v₁, p₂, q₂, u₂, v₂]

theorem first_frame_low_output :
    leray (sub p₁ q₁) (symSymbol (sub p₁ q₁) u₁ v₁) = ⟨0, -4, 0⟩ := by
  unfold leray symSymbol
  apply V3.ext <;>
    norm_num [dot, add, sub, smul, p₁, q₁, u₁, v₁]

theorem second_frame_low_output :
    leray (sub p₂ q₂) (symSymbol (sub p₂ q₂) u₂ v₂) = ⟨0, 0, -4⟩ := by
  unfold leray symSymbol
  apply V3.ext <;>
    norm_num [dot, add, sub, smul, p₂, q₂, u₂, v₂]

theorem two_frame_cross_pollution :
    leray (add p₁ p₂) (symSymbol (add p₁ p₂) u₁ u₂) = ⟨2, -2, 2⟩ := by
  unfold leray symSymbol
  apply V3.ext <;>
    norm_num [dot, add, sub, smul, p₁, p₂, u₁, u₂]

theorem two_frame_cross_pollution_ne_zero :
    leray (add p₁ p₂) (symSymbol (add p₁ p₂) u₁ u₂) ≠ zero := by
  rw [two_frame_cross_pollution]
  intro h
  have hx := congrArg V3.x h
  norm_num [zero] at hx

/-- The four sign patterns form a Hadamard system. This is the scalar core of
an antipodal two-frame cancellation firewall. -/
theorem four_fiber_hadamard_no_go
    (A B C D X Y Z W : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hpp : A * X + B * Y - C * Z + D * W = 0)
    (hpn : A * X + B * Y + C * Z - D * W = 0)
    (hnp : -A * X + B * Y + C * Z + D * W = 0)
    (hnn : -A * X + B * Y - C * Z - D * W = 0) :
    X = 0 ∧ Y = 0 ∧ Z = 0 ∧ W = 0 := by
  have hAX : A * X = 0 := by linarith
  have hBY : B * Y = 0 := by linarith
  have hCZ : C * Z = 0 := by linarith
  have hDW : D * W = 0 := by linarith
  exact ⟨(mul_eq_zero.mp hAX).resolve_left hA,
    (mul_eq_zero.mp hBY).resolve_left hB,
    (mul_eq_zero.mp hCZ).resolve_left hC,
    (mul_eq_zero.mp hDW).resolve_left hD⟩

/-- The real shadow of the same-shell chord conditions: equality and negative
equality force both frame ratios to vanish. -/
theorem real_two_chord_no_go (t s : ℝ) (h₁ : t = s) (h₂ : t = -s) :
    t = 0 ∧ s = 0 := by
  constructor <;> linarith

#print axioms carrier_transverse
#print axioms equal_shell_and_norm
#print axioms high_symbol_parallel
#print axioms high_leray_zero
#print axioms low_symbol_exact
#print axioms low_leray_exact
#print axioms normalized_coefficient_identity
#print axioms quadratic_moment_code
#print axioms two_frame_carrier_transverse
#print axioms first_frame_low_output
#print axioms second_frame_low_output
#print axioms two_frame_cross_pollution
#print axioms two_frame_cross_pollution_ne_zero
#print axioms four_fiber_hadamard_no_go
#print axioms real_two_chord_no_go

end NSSelectiveLerayAtom
