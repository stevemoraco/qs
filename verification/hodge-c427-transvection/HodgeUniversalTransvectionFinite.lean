import Mathlib

namespace Millennium.Hodge.C427

abbrev V := Fin 3 → ℚ

def e : V := ![1, 0, 0]
def f : V := ![0, 1, 0]
def v : V := ![0, 0, 1]

def form (q : ℚ) (x y : V) : ℚ :=
  x 0 * y 1 + x 1 * y 0 + q * x 2 * y 2

def transvection (q : ℚ) (x : V) : V :=
  ![x 0 - q * x 2 - q * x 1 / 2, x 1, x 2 + x 1]

def inverseTransvection (q : ℚ) (x : V) : V :=
  ![x 0 + q * x 2 - q * x 1 / 2, x 1, x 2 - x 1]

theorem hyperbolic_relations (q : ℚ) :
    form q e e = 0 ∧ form q f f = 0 ∧ form q e f = 1 ∧
      form q e v = 0 ∧ form q f v = 0 ∧ form q v v = q := by
  simp [form, e, f, v]

theorem transvection_isometry (q : ℚ) (x y : V) :
    form q (transvection q x) (transvection q y) = form q x y := by
  simp [form, transvection]
  ring

theorem inverse_left (q : ℚ) (x : V) :
    inverseTransvection q (transvection q x) = x := by
  funext i
  fin_cases i <;> simp [transvection, inverseTransvection] <;> ring

theorem inverse_right (q : ℚ) (x : V) :
    transvection q (inverseTransvection q x) = x := by
  funext i
  fin_cases i <;> simp [transvection, inverseTransvection] <;> ring

theorem fixes_e (q : ℚ) : transvection q e = e := by
  funext i
  fin_cases i <;> simp [transvection, e]

theorem image_f (q : ℚ) :
    transvection q f = f + v - (q / 2) • e := by
  funext i
  fin_cases i <;> simp [transvection, e, f, v] <;> ring

theorem rank_two_coordinate (q : ℚ) (x : V) :
    (transvection q x - x) 1 = 0 := by
  simp [transvection]

theorem extract_v_from_image
    (Alg : V → Prop)
    (hsub : ∀ {x y}, Alg x → Alg y → Alg (x - y))
    (hadd : ∀ {x y}, Alg x → Alg y → Alg (x + y))
    (hsmul : ∀ c {x}, Alg x → Alg (c • x))
    (q : ℚ)
    (hTf : Alg (transvection q f))
    (hf : Alg f)
    (he : Alg e) :
    Alg v := by
  have hcomb : Alg ((transvection q f - f) + (q / 2) • e) :=
    hadd (hsub hTf hf) (hsmul (q / 2) he)
  have hid : (transvection q f - f) + (q / 2) • e = v := by
    funext i
    fin_cases i <;> simp [transvection, e, f, v] <;> ring
  simpa [hid] using hcomb

theorem stabilized_middle_codimension {d p : ℕ} (hp : p ≤ d) :
    p + (d - p) = d := Nat.add_sub_of_le hp

#print axioms hyperbolic_relations
#print axioms transvection_isometry
#print axioms inverse_left
#print axioms inverse_right
#print axioms fixes_e
#print axioms image_f
#print axioms rank_two_coordinate
#print axioms extract_v_from_image
#print axioms stabilized_middle_codimension

end Millennium.Hodge.C427
