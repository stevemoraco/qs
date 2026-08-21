import Mathlib

namespace Millennium.Hodge

/-- Trace on the 20-dimensional transcendental block of `a I + b M`,
where `Tr(M)=0`. -/
def rm13Trace (a b : ℚ) : ℚ := 20 * a

/-- Trace of the square of `a I + b M`, using `M^2 = 13 I`. -/
def rm13TraceSq (a b : ℚ) : ℚ := 20 * (a ^ 2 + 13 * b ^ 2)

/-- The scalar-free quadratic trace discriminant. -/
def rm13Disc (a b : ℚ) : ℚ :=
  20 * rm13TraceSq a b - (rm13Trace a b) ^ 2

/-- The trace discriminant is exactly `5200 b^2`. -/
theorem rm13Disc_formula (a b : ℚ) :
    rm13Disc a b = 5200 * b ^ 2 := by
  unfold rm13Disc rm13TraceSq rm13Trace
  ring

/-- Vanishing of the trace discriminant is exactly vanishing of the RM coefficient. -/
theorem rm13Disc_eq_zero_iff (a b : ℚ) :
    rm13Disc a b = 0 ↔ b = 0 := by
  rw [rm13Disc_formula]
  norm_num

/-- Nonvanishing of the trace discriminant is exactly nonscalarity. -/
theorem rm13Disc_ne_zero_iff (a b : ℚ) :
    rm13Disc a b ≠ 0 ↔ b ≠ 0 := by
  rw [not_congr (rm13Disc_eq_zero_iff a b)]

/-- Trace of the product `(a I + b M)(c I + d M)`. -/
def rm13MixedTrace (a b c d : ℚ) : ℚ :=
  20 * (a * c + 13 * b * d)

/-- Bilinear polarization of the trace discriminant. -/
def rm13Beta (a b c d : ℚ) : ℚ :=
  20 * rm13MixedTrace a b c d - rm13Trace a b * rm13Trace c d

/-- The bilinear trace form sees only the two RM coefficients. -/
theorem rm13Beta_formula (a b c d : ℚ) :
    rm13Beta a b c d = 5200 * b * d := by
  unfold rm13Beta rm13MixedTrace rm13Trace
  ring

/-- The quadratic discriminant is the self-pairing of the bilinear trace form. -/
theorem rm13Beta_self (a b : ℚ) :
    rm13Beta a b a b = rm13Disc a b := by
  rw [rm13Beta_formula, rm13Disc_formula]
  ring

/-- If every element of a family has zero trace discriminant, every RM coefficient is zero. -/
theorem scalar_of_zero_disc {ι : Type} (a b : ι → ℚ)
    (h : ∀ i, rm13Disc (a i) (b i) = 0) :
    ∀ i, b i = 0 := by
  intro i
  exact (rm13Disc_eq_zero_iff (a i) (b i)).mp (h i)

#print axioms rm13Disc_formula
#print axioms rm13Disc_eq_zero_iff
#print axioms rm13Disc_ne_zero_iff
#print axioms rm13Beta_formula
#print axioms rm13Beta_self
#print axioms scalar_of_zero_disc

end Millennium.Hodge
