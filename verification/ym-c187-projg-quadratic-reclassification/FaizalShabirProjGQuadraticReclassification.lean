import Mathlib

/-!
# ProjG quadratic-reclassification firewall

Finite real-algebra firewall for the Faizal--Shabir Lemma 6.6 / Theorem 6.7
bookkeeping issue isolated in C187.

The manuscript says that the nearest-group projection `ProjG` differs from the
identity by an analytic map and that its connected contributions are of higher
polymer order.  Higher order is a *quadratic small-field currency*; it is not,
by itself, an independent geometric-in-scale tail such as `b^{-gamma k}`.

The declarations below record only that finite bookkeeping distinction and a
scalar two-unit variance identity mirroring the matrix identity behind averaging
unitaries.  They do not formalize SU(N), the polar projection, polymer RG,
BKAR, Yang--Mills, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirProjGQuadraticReclassification

/-- A projection correction that is quadratic in the current activity should be
absorbed into the existing quadratic small-field term, leaving only the genuine
scale tail as an additive remainder. -/
theorem quadratic_projection_reclassifies
    (x small proj tail total C K : ℝ)
    (hsmall : small ≤ C * x ^ 2)
    (hproj : proj ≤ K * x ^ 2)
    (htotal : total ≤ small + proj + tail) :
    total ≤ (C + K) * x ^ 2 + tail := by
  nlinarith

/-- Package form: two quadratic contributions combine into one quadratic
coefficient without manufacturing any new scale-decay hypothesis. -/
theorem combine_quadratic_small_field_terms
    (x a b A B : ℝ)
    (ha : a ≤ A * x ^ 2)
    (hb : b ≤ B * x ^ 2) :
    a + b ≤ (A + B) * x ^ 2 := by
  nlinarith

/-- "Higher order" is not the same statement as a geometric scale tail.
At the fixed small-field value `x = 1/2`, the quadratic correction is `1/4`,
which already exceeds the third geometric dyadic scale `1/8`. -/
theorem quadratic_order_is_not_a_dyadic_scale_tail :
    ((1 / 2 : ℝ) ^ 2) > ((1 / 2 : ℝ) ^ 3) := by
  norm_num

/-- Exact scalar analogue of the pairwise-variance identity for an average of
two unitary matrices.  If `u^2 = v^2 = 1`, the defect of the squared average
from one is quadratic in their spread. -/
theorem two_unit_scalar_variance_identity
    (u v : ℝ)
    (hu : u ^ 2 = 1)
    (hv : v ^ 2 = 1) :
    1 - ((u + v) / 2) ^ 2 = (u - v) ^ 2 / 4 := by
  nlinarith

/-- On the diagonal (`u = v`) the scalar averaging defect vanishes exactly. -/
theorem diagonal_average_has_zero_variance
    (u : ℝ)
    (hu : u ^ 2 = 1) :
    1 - ((u + u) / 2) ^ 2 = 0 := by
  nlinarith

#print axioms quadratic_projection_reclassifies
#print axioms combine_quadratic_small_field_terms
#print axioms quadratic_order_is_not_a_dyadic_scale_tail
#print axioms two_unit_scalar_variance_identity
#print axioms diagonal_average_has_zero_variance

end Millennium.YangMills.FaizalShabirProjGQuadraticReclassification
