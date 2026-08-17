import Mathlib

namespace Millennium.Hodge.Bidegree24ProductEightParityElimination

def EvenZ (n : ℤ) : Prop := ∃ k : ℤ, n = 2 * k

def OddZ (n : ℤ) : Prop := ∃ k : ℤ, n = 2 * k + 1

theorem traceHalf_det_identity (a b c d : ℤ) :
    a * d - 2 * a * c + b * c + 2 * c * d - 2 * c ^ 2 =
      (a * d - b * c) + 2 * c * (-a + b + d - c) := by
  ring

theorem det_odd_of_traceHalf_odd (a b c d : ℤ)
    (hodd : OddZ (a * d - 2 * a * c + b * c + 2 * c * d - 2 * c ^ 2)) :
    OddZ (a * d - b * c) := by
  rcases hodd with ⟨k, hk⟩
  refine ⟨k - c * (-a + b + d - c), ?_⟩
  calc
    a * d - b * c =
        (a * d - 2 * a * c + b * c + 2 * c * d - 2 * c ^ 2) -
          2 * c * (-a + b + d - c) := by ring
    _ = (2 * k + 1) - 2 * c * (-a + b + d - c) := by rw [hk]
    _ = 2 * (k - c * (-a + b + d - c)) + 1 := by ring

theorem coordinates_even_of_odd_det
    (a b c d x y : ℤ)
    (hdet : OddZ (a * d - b * c))
    (hfirst : EvenZ (a * x + b * y))
    (hsecond : EvenZ (c * x + d * y)) :
    EvenZ x ∧ EvenZ y := by
  rcases hdet with ⟨k, hk⟩
  rcases hfirst with ⟨u, hu⟩
  rcases hsecond with ⟨v, hv⟩
  constructor
  · refine ⟨d * u - b * v - k * x, ?_⟩
    have hxdet : (a * d - b * c) * x = 2 * (d * u - b * v) := by
      calc
        (a * d - b * c) * x =
            d * (a * x + b * y) - b * (c * x + d * y) := by ring
        _ = d * (2 * u) - b * (2 * v) := by rw [hu, hv]
        _ = 2 * (d * u - b * v) := by ring
    calc
      x = (a * d - b * c) * x - 2 * k * x := by rw [hk]; ring
      _ = 2 * (d * u - b * v) - 2 * k * x := by rw [hxdet]
      _ = 2 * (d * u - b * v - k * x) := by ring
  · refine ⟨a * v - c * u - k * y, ?_⟩
    have hydet : (a * d - b * c) * y = 2 * (a * v - c * u) := by
      calc
        (a * d - b * c) * y =
            a * (c * x + d * y) - c * (a * x + b * y) := by ring
        _ = a * (2 * v) - c * (2 * u) := by rw [hu, hv]
        _ = 2 * (a * v - c * u) := by ring
    calc
      y = (a * d - b * c) * y - 2 * k * y := by rw [hk]; ring
      _ = 2 * (a * v - c * u) - 2 * k * y := by rw [hydet]
      _ = 2 * (a * v - c * u - k * y) := by ring

theorem traceHalf_odd_of_even_square (H Dsq s : ℤ)
    (hsq : Dsq = 2 * s)
    (htrace : 2 * H = 10 - 2 * Dsq) : OddZ H := by
  refine ⟨2 - s, ?_⟩
  omega

theorem determinant_coordinates_even
    (a b c d x y H Dsq s : ℤ)
    (hhalf : H = a * d - 2 * a * c + b * c + 2 * c * d - 2 * c ^ 2)
    (hsq : Dsq = 2 * s)
    (htrace : 2 * H = 10 - 2 * Dsq)
    (hfirst : EvenZ (a * x + b * y))
    (hsecond : EvenZ (c * x + d * y)) :
    EvenZ x ∧ EvenZ y := by
  have hoddH := traceHalf_odd_of_even_square H Dsq s hsq htrace
  have hoddTrace :
      OddZ (a * d - 2 * a * c + b * c + 2 * c * d - 2 * c ^ 2) := by
    simpa [hhalf] using hoddH
  have hdet := det_odd_of_traceHalf_odd a b c d hoddTrace
  exact coordinates_even_of_odd_det a b c d x y hdet hfirst hsecond

theorem forced_multiple_section (a b m : ℤ)
    (ha : 1 ≤ a) (hb : b ≤ a - 1)
    (hintersection : 0 ≤ 4 * (b - 2 * a) + 2 * m) :
    4 ≤ m := by
  omega

theorem odd_det_cannot_send_section_even
    (a b c d : ℤ)
    (hdet : OddZ (a * d - b * c))
    (hfirst : EvenZ (-2 * a + b))
    (hsecond : EvenZ (-2 * c + d)) : False := by
  rcases hfirst with ⟨u, hu⟩
  rcases hsecond with ⟨v, hv⟩
  have hfirst' : EvenZ (a * (-2) + b * 1) := by
    refine ⟨u, ?_⟩
    calc
      a * (-2) + b * 1 = -2 * a + b := by ring
      _ = 2 * u := hu
  have hsecond' : EvenZ (c * (-2) + d * 1) := by
    refine ⟨v, ?_⟩
    calc
      c * (-2) + d * 1 = -2 * c + d := by ring
      _ = 2 * v := hv
  have hcoords := coordinates_even_of_odd_det a b c d (-2) 1 hdet hfirst' hsecond'
  rcases hcoords.2 with ⟨k, hk⟩
  omega

theorem productEight_parity_contradiction
    (a b c d H Dsq s : ℤ)
    (hhalf : H = a * d - 2 * a * c + b * c + 2 * c * d - 2 * c ^ 2)
    (hsq : Dsq = 2 * s)
    (htrace : 2 * H = 10 - 2 * Dsq)
    (hRfirst : EvenZ (-2 * a + b))
    (hRsecond : EvenZ (-2 * c + d)) : False := by
  have hoddH := traceHalf_odd_of_even_square H Dsq s hsq htrace
  have hoddTrace :
      OddZ (a * d - 2 * a * c + b * c + 2 * c * d - 2 * c ^ 2) := by
    simpa [hhalf] using hoddH
  have hdet := det_odd_of_traceHalf_odd a b c d hoddTrace
  exact odd_det_cannot_send_section_even a b c d hdet hRfirst hRsecond

#print axioms traceHalf_det_identity
#print axioms det_odd_of_traceHalf_odd
#print axioms coordinates_even_of_odd_det
#print axioms traceHalf_odd_of_even_square
#print axioms determinant_coordinates_even
#print axioms forced_multiple_section
#print axioms odd_det_cannot_send_section_even
#print axioms productEight_parity_contradiction

end Millennium.Hodge.Bidegree24ProductEightParityElimination
