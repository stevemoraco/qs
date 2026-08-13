import Mathlib

/-!
Finite algebraic core of a selective Euler/Leray interaction.

This file proves only exact vector and polynomial identities.  It does not
construct a Navier--Stokes solution, a recursively closed packet family, or a
Clay-problem blow-up solution.
-/

namespace NSSelectiveLerayAtom

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
noncomputable def leray (k s : V3) : V3 :=
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

/-! The same atom in coordinates adapted to its invariant plane.  The first
two coordinates form a planar incompressible velocity; the third coordinate
is passive.  The retained low output is purely in that passive direction. -/

def p3 (a H : ℝ) : V3 := ⟨a, H, 0⟩
def q3 (a H : ℝ) : V3 := ⟨-a, H, 0⟩
def u3 (a H c : ℝ) : V3 := ⟨-H, a, c * H⟩
def v3 (a H c : ℝ) : V3 := ⟨-H, -a, c * H⟩

theorem passive_carrier_transverse (a H c : ℝ) :
    dot (p3 a H) (u3 a H c) = 0 ∧
    dot (q3 a H) (v3 a H c) = 0 := by
  constructor <;> simp [dot, p3, q3, u3, v3] <;> ring

theorem passive_high_symbol_parallel (a H c : ℝ) :
    symSymbol (add (p3 a H) (q3 a H)) (u3 a H c) (v3 a H c) =
      smul (-2 * a ^ 2) (add (p3 a H) (q3 a H)) := by
  apply V3.ext <;>
    simp [symSymbol, add, smul, dot, p3, q3, u3, v3] <;>
    ring

theorem passive_high_leray_zero (a H c : ℝ) :
    leray (add (p3 a H) (q3 a H))
      (symSymbol (add (p3 a H) (q3 a H)) (u3 a H c) (v3 a H c)) =
      zero := by
  rw [passive_high_symbol_parallel]
  unfold leray
  apply V3.ext <;>
    simp [add, sub, smul, dot, p3, q3, zero] <;>
    field_simp <;>
    ring

theorem passive_low_leray_exact (a H c : ℝ) :
    leray (sub (p3 a H) (q3 a H))
      (symSymbol (sub (p3 a H) (q3 a H)) (u3 a H c) (v3 a H c)) =
      ⟨0, 0, -4 * c * a * H ^ 2⟩ := by
  unfold leray symSymbol
  apply V3.ext <;>
    simp [add, sub, smul, dot, p3, q3, u3, v3] <;>
    field_simp <;>
    ring

/-! A hostile integer witness for the isosceles one-polarization relay.
The desired sum and pump-conjugate cancellation are exact, but a reciprocal
interaction is not contained in the selected pump polarization.  It creates
a nonzero orthogonal polarization at the same carrier. -/

def isoP : V3 := ⟨1, 0, 0⟩
def isoQ : V3 := ⟨0, 1, 0⟩
def isoK : V3 := ⟨-1, -1, 0⟩
def isoA : V3 := ⟨0, 1, -1⟩
def isoB : V3 := ⟨-1, 0, 1⟩
def isoN : V3 := ⟨0, 0, 1⟩
def isoR : V3 := ⟨0, 1, 1⟩

theorem isosceles_carrier_relation :
    add (add isoP isoQ) isoK = zero := by
  apply V3.ext <;>
    norm_num [add, isoP, isoQ, isoK, zero]

theorem isosceles_carrier_transverse :
    dot isoP isoA = 0 ∧ dot isoQ isoB = 0 ∧ dot isoK isoN = 0 := by
  norm_num [dot, isoP, isoQ, isoK, isoA, isoB, isoN]

theorem isosceles_active_sum :
    leray (add isoP isoQ) (symSymbol (add isoP isoQ) isoA isoB) =
      ⟨0, 0, 2⟩ := by
  unfold leray symSymbol
  apply V3.ext <;>
    norm_num [dot, add, sub, smul, isoP, isoQ, isoA, isoB]

theorem isosceles_conjugate_difference_killed :
    leray (sub isoP isoQ) (symSymbol (sub isoP isoQ) isoA isoB) =
      zero := by
  unfold leray symSymbol
  apply V3.ext <;>
    norm_num [dot, add, sub, smul, isoP, isoQ, isoA, isoB, zero]

theorem isosceles_reciprocal_full_output :
    leray (add isoQ isoK) (symSymbol (add isoQ isoK) isoB isoN) =
      isoN := by
  unfold leray symSymbol
  apply V3.ext <;>
    norm_num [dot, add, sub, smul, isoQ, isoK, isoB, isoN]

theorem isosceles_reciprocal_decomposition :
    isoN = add (smul (-(1 : ℝ) / 2) isoA) (smul ((1 : ℝ) / 2) isoR) := by
  apply V3.ext <;>
    norm_num [add, smul, isoN, isoA, isoR]

theorem isosceles_orthogonal_leakage :
    dot isoA isoR = 0 ∧ dot (add isoQ isoK) isoR = 0 ∧ isoR ≠ zero := by
  constructor
  · norm_num [dot, isoA, isoR]
  constructor
  · norm_num [dot, add, isoQ, isoK, isoR]
  · intro h
    have hy := congrArg V3.y h
    norm_num [isoR, zero] at hy

theorem isosceles_reciprocal_not_in_selected_polarization :
    ∀ t : ℝ, isoN ≠ smul t isoA := by
  intro t h
  have hy := congrArg V3.y h
  have hz := congrArg V3.z h
  norm_num [isoN, smul, isoA] at hy hz
  linarith

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
#print axioms passive_carrier_transverse
#print axioms passive_high_symbol_parallel
#print axioms passive_high_leray_zero
#print axioms passive_low_leray_exact
#print axioms isosceles_carrier_relation
#print axioms isosceles_carrier_transverse
#print axioms isosceles_active_sum
#print axioms isosceles_conjugate_difference_killed
#print axioms isosceles_reciprocal_full_output
#print axioms isosceles_reciprocal_decomposition
#print axioms isosceles_orthogonal_leakage
#print axioms isosceles_reciprocal_not_in_selected_polarization

end NSSelectiveLerayAtom
