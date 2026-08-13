import Mathlib

namespace SixLaneAudit.NSPolarizationBundleClosure

@[ext]
structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

def dot (u v : V3) : ℝ := u.x * v.x + u.y * v.y + u.z * v.z

def add (u v : V3) : V3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

def sub (u v : V3) : V3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩

def smul (a : ℝ) (u : V3) : V3 := ⟨a * u.x, a * u.y, a * u.z⟩

def symSymbol (k u v : V3) : V3 :=
  add (smul (dot u k) v) (smul (dot v k) u)

noncomputable def leray (k s : V3) : V3 :=
  sub s (smul (dot s k / dot k k) k)

theorem dot_comm (u v : V3) : dot u v = dot v u := by
  simp [dot]
  ring

theorem dot_sub_right (u v w : V3) :
    dot u (sub v w) = dot u v - dot u w := by
  simp [dot, sub]
  ring

theorem dot_smul_right (u v : V3) (a : ℝ) :
    dot u (smul a v) = a * dot u v := by
  simp [dot, smul]
  ring

/-- At every nonzero carrier, the explicit Leray projector lands in the full
transverse polarization fiber. -/
theorem leray_transverse (k s : V3) (hkk : dot k k ≠ 0) :
    dot k (leray k s) = 0 := by
  calc
    dot k (leray k s) =
        dot k s - dot k (smul (dot s k / dot k k) k) := by
      rw [show leray k s = sub s (smul (dot s k / dot k k) k) by rfl]
      exact dot_sub_right k s (smul (dot s k / dot k k) k)
    _ = dot k s - (dot s k / dot k k) * dot k k := by
      rw [dot_smul_right]
    _ = dot s k - (dot s k / dot k k) * dot k k := by
      rw [dot_comm k s]
    _ = 0 := by
      rw [div_mul_cancel₀ (dot s k) hkk]
      ring

/-- Carrier and two polarization lines at the reciprocal `-P` fiber. -/
def isoCarrier : V3 := ⟨-1, 0, 0⟩
def isoA : V3 := ⟨0, 1, -1⟩
def isoR : V3 := ⟨0, 1, 1⟩

/-- Remaining carriers and selected polarizations of the hostile isosceles
relay. -/
def isoP : V3 := ⟨1, 0, 0⟩
def isoQ : V3 := ⟨0, 1, 0⟩
def isoK : V3 := ⟨-1, -1, 0⟩
def isoB : V3 := ⟨-1, 0, 1⟩
def isoN : V3 := ⟨0, 0, 1⟩

theorem iso_transverse_iff_x_zero (s : V3) :
    dot isoCarrier s = 0 ↔ s.x = 0 := by
  simp [dot, isoCarrier]

/-- `isoA` and the leaked orthogonal line `isoR` span the entire transverse
fiber at the reciprocal carrier. -/
theorem iso_two_polarizations_span_transverse (s : V3)
    (hs : dot isoCarrier s = 0) :
    s = add (smul ((s.y - s.z) / 2) isoA)
      (smul ((s.y + s.z) / 2) isoR) := by
  have hx : s.x = 0 := (iso_transverse_iff_x_zero s).mp hs
  apply V3.ext <;>
    simp [add, smul, isoA, isoR, hx] <;>
    ring

/-- Every Leray-projected output at the reciprocal carrier belongs to the
full two-polarization bundle. -/
theorem iso_leray_output_in_two_polarization_bundle (s : V3) :
    leray isoCarrier s =
      add
        (smul (((leray isoCarrier s).y - (leray isoCarrier s).z) / 2) isoA)
        (smul (((leray isoCarrier s).y + (leray isoCarrier s).z) / 2) isoR) := by
  apply iso_two_polarizations_span_transverse
  apply leray_transverse
  norm_num [dot, isoCarrier]

/-- One selected line is genuinely insufficient at this reciprocal fiber. -/
theorem isoR_not_in_isoA_line :
    ∀ t : ℝ, isoR ≠ smul t isoA := by
  intro t h
  have hy := congrArg V3.y h
  have hz := congrArg V3.z h
  norm_num [isoR, isoA, smul] at hy hz
  linarith

/-- The original selected `A/B` pair has exact conjugate-difference
cancellation. -/
theorem selected_line_kills_conjugate_difference :
    leray (sub isoP isoQ)
      (symSymbol (sub isoP isoQ) isoA isoB) = ⟨0, 0, 0⟩ := by
  unfold leray symSymbol
  apply V3.ext <;>
    norm_num [dot, add, sub, smul, isoP, isoQ, isoA, isoB]

/-- Admitting the leaked orthogonal polarization `isoR` reopens the previously
killed exterior difference `P-Q`. -/
theorem leaked_line_reopens_conjugate_difference :
    leray (sub isoP isoQ)
      (symSymbol (sub isoP isoQ) isoR isoB) = ⟨0, 0, -2⟩ := by
  unfold leray symSymbol
  apply V3.ext <;>
    norm_num [dot, add, sub, smul, isoP, isoQ, isoR, isoB]

theorem leaked_line_reopens_conjugate_difference_ne_zero :
    leray (sub isoP isoQ)
      (symSymbol (sub isoP isoQ) isoR isoB) ≠ ⟨0, 0, 0⟩ := by
  rw [leaked_line_reopens_conjugate_difference]
  intro h
  have hz := congrArg V3.z h
  norm_num at hz

/-- The reciprocal `Q+K=-P` interaction that forced the polarization repair. -/
theorem reciprocal_selected_pair_output :
    leray (add isoQ isoK)
      (symSymbol (add isoQ isoK) isoB isoN) = isoN := by
  unfold leray symSymbol
  apply V3.ext <;>
    norm_num [dot, add, sub, smul, isoQ, isoK, isoB, isoN]

/-- With scalar amplitudes `b,c`, the reciprocal output scales as `b*c` and
contains a forced `isoR` coefficient `(b*c)/2`. -/
theorem scaled_reciprocal_output_decomposition (b c : ℝ) :
    smul (b * c) isoN =
      add (smul (-(b * c) / 2) isoA) (smul ((b * c) / 2) isoR) := by
  apply V3.ext <;>
    simp [smul, add, isoN, isoA, isoR] <;>
    ring

/-- Exact coefficient-level second-generation leak.  Once the reciprocal
interaction has generated its forced `R` coefficient `(b*c)/2`, pairing it
with the real conjugate `Q` amplitude `b` produces the exterior `P-Q` mode with
z-amplitude `-b^2*c`. -/
theorem forced_second_generation_exterior (b c : ℝ) :
    leray (sub isoP isoQ)
      (symSymbol (sub isoP isoQ)
        (smul ((b * c) / 2) isoR) (smul b isoB)) =
      ⟨0, 0, -(b ^ 2 * c)⟩ := by
  unfold leray symSymbol
  apply V3.ext <;>
    norm_num [dot, add, sub, smul, isoP, isoQ, isoR, isoB] <;>
    ring

/-- Therefore, inside the isolated triad, nonzero reciprocal-driving
amplitudes force a genuinely nonzero exterior contribution at the next
bilinear interaction. -/
theorem forced_second_generation_exterior_ne_zero
    {b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0) :
    leray (sub isoP isoQ)
      (symSymbol (sub isoP isoQ)
        (smul ((b * c) / 2) isoR) (smul b isoB)) ≠ ⟨0, 0, 0⟩ := by
  rw [forced_second_generation_exterior]
  intro h
  have hz : -(b ^ 2 * c) = 0 := by
    simpa using congrArg V3.z h
  have hzero : b ^ 2 * c = 0 := neg_eq_zero.mp hz
  exact (mul_ne_zero (pow_ne_zero 2 hb) hc) hzero

#print axioms dot_comm
#print axioms dot_sub_right
#print axioms dot_smul_right
#print axioms leray_transverse
#print axioms iso_transverse_iff_x_zero
#print axioms iso_two_polarizations_span_transverse
#print axioms iso_leray_output_in_two_polarization_bundle
#print axioms isoR_not_in_isoA_line
#print axioms selected_line_kills_conjugate_difference
#print axioms leaked_line_reopens_conjugate_difference
#print axioms leaked_line_reopens_conjugate_difference_ne_zero
#print axioms reciprocal_selected_pair_output
#print axioms scaled_reciprocal_output_decomposition
#print axioms forced_second_generation_exterior
#print axioms forced_second_generation_exterior_ne_zero

end SixLaneAudit.NSPolarizationBundleClosure
