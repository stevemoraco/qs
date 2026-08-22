import Mathlib

/-!
# RH B202 BGST crossing-margin finite core

Finite real algebra behind the B202/B202A/B202B producer preflight.

Formalized here:
* if `delta < rho <= 2*delta`, the normalized imaginary height `delta/rho`
  lies in `[1/2,1)`; the strict lower inequality excludes tangency;
* the exact quadratic-form witness for the normalized 2x2 conjugate-pair
  crossing block;
* the universal `2/7` entering-sign negative Rayleigh margin when the normalized
  imaginary height is at least one half;
* the more general geometric-ratio margin once `kappa^2*b^2 >= 1`;
* coefficient-only 2x2 jump identities and the `j0/7` negative witness;
* the leaving-sign block has an even larger negative witness;
* a generic normalized negative margin `c*T` transfers to B200 soft response
  at least `c/(1+c)`;
* in particular `(2/7)T` negative depth contributes at least `2/9`.

This file does NOT formalize Xi, contour integrals, Hankel reconstruction,
Deng--Yang--Lu's crossing theorem, primes, zeta, RH, B46, or any BGST-to-prime
transporter.
-/

namespace RHB202BGSTCrossingMarginFinite

/-- A genuine crossing radius within a factor two of the vertical displacement
gives normalized imaginary height at least one half and strictly below one.
The strict hypothesis `delta < rho` excludes the tangent case. -/
theorem normalized_height_half
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hlo : delta < rho)
    (hhi : rho ≤ 2 * delta) :
    (1 / 2 : ℝ) ≤ delta / rho ∧ delta / rho < 1 := by
  have hrho : 0 < rho := lt_trans hdelta hlo
  constructor
  · apply (le_div_iff₀ hrho).2
    nlinarith
  · apply (div_lt_iff₀ hrho).2
    simpa using hlo

/-- Normalized entering-sign quadratic form for a conjugate-pair 2x2 crossing
block, after dividing by the common multiplicity. -/
def pairQ (a b x y : ℝ) : ℝ :=
  2 * (x ^ 2 + 2 * a * x * y + (a ^ 2 - b ^ 2) * y ^ 2)

/-- The explicit vector `(-a,1)` sees exactly the negative `b^2` direction. -/
theorem pairQ_witness (a b : ℝ) :
    pairQ a b (-a) 1 = -2 * b ^ 2 := by
  simp [pairQ]
  ring

/-- On the unit circle, normalized imaginary height at least one half gives a
uniform negative Rayleigh margin `2/7` for the entering-sign block. -/
theorem entering_pair_margin
    {a b : ℝ}
    (hcircle : a ^ 2 + b ^ 2 = 1)
    (hb : (1 / 4 : ℝ) ≤ b ^ 2) :
    pairQ a b (-a) 1 ≤ -(2 / 7 : ℝ) * (a ^ 2 + 1) := by
  rw [pairQ_witness]
  nlinarith

/-- Geometric-ratio version of the entering-sign margin.  The hypothesis
`1 <= kappa^2*b^2` is exactly the squared form of `|b| >= 1/kappa`. -/
theorem entering_pair_margin_kappa
    {a b kappa : ℝ}
    (hkappa : 1 < kappa)
    (hcircle : a ^ 2 + b ^ 2 = 1)
    (hb : 1 ≤ kappa ^ 2 * b ^ 2) :
    pairQ a b (-a) 1 ≤
      -(2 / (2 * kappa ^ 2 - 1)) * (a ^ 2 + 1) := by
  have hkappa2 : 1 < kappa ^ 2 := by nlinarith
  have hden : 0 < 2 * kappa ^ 2 - 1 := by nlinarith
  have hcore :
      (2 / (2 * kappa ^ 2 - 1)) * (a ^ 2 + 1) ≤ 2 * b ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    nlinarith
  rw [pairQ_witness]
  nlinarith

/-- Quadratic form of a real symmetric order-two jump matrix
`[[j0,j1],[j1,j2]]`. -/
def coeffQ (j0 j1 j2 x y : ℝ) : ℝ :=
  j0 * x ^ 2 + 2 * j1 * x * y + j2 * y ^ 2

/-- The coefficient-defined vector `(-j1,j0)` evaluates to `j0*det(J)`. -/
theorem coeffQ_witness (j0 j1 j2 : ℝ) :
    coeffQ j0 j1 j2 (-j1) j0 =
      j0 * (j0 * j2 - j1 ^ 2) := by
  simp [coeffQ]
  ring

/-- Coefficient-only version of the dyadic entering-sign margin.  The first
hypothesis is the unit-circle moment identity after clearing denominators; the
second is exactly the determinant form of normalized height at least one half.
No recovered node coordinate appears in the conclusion. -/
theorem coefficient_only_entering_margin
    {j0 j1 j2 : ℝ}
    (hj0 : 0 < j0)
    (hcircle : 2 * j1 ^ 2 - j0 * j2 = j0 ^ 2)
    (hdet : j0 ^ 2 / 4 ≤ j1 ^ 2 - j0 * j2) :
    coeffQ j0 j1 j2 (-j1) j0 ≤
      -(j0 / 7) * (j1 ^ 2 + j0 ^ 2) := by
  have hdetneg : j0 * j2 - j1 ^ 2 ≤ -(j0 ^ 2 / 4) := by
    nlinarith
  have hj1 : j1 ^ 2 ≤ (3 / 4 : ℝ) * j0 ^ 2 := by
    nlinarith
  have hnorm : j1 ^ 2 + j0 ^ 2 ≤ (7 / 4 : ℝ) * j0 ^ 2 := by
    nlinarith
  have hq :
      j0 * (j0 * j2 - j1 ^ 2) ≤ j0 * (-(j0 ^ 2 / 4)) :=
    mul_le_mul_of_nonneg_left hdetneg (le_of_lt hj0)
  have hneg :
      -(j0 / 7) * ((7 / 4 : ℝ) * j0 ^ 2) ≤
        -(j0 / 7) * (j1 ^ 2 + j0 ^ 2) := by
    apply mul_le_mul_of_nonpos_left hnorm
    nlinarith
  calc
    coeffQ j0 j1 j2 (-j1) j0 =
        j0 * (j0 * j2 - j1 ^ 2) := coeffQ_witness j0 j1 j2
    _ ≤ j0 * (-(j0 ^ 2 / 4)) := hq
    _ = -(j0 / 7) * ((7 / 4 : ℝ) * j0 ^ 2) := by ring
    _ ≤ -(j0 / 7) * (j1 ^ 2 + j0 ^ 2) := hneg

/-- Reversing the crossing sign has an explicit unit-vector negative witness of
size two, hence certainly at least the `2/7` universal margin. -/
theorem leaving_pair_margin (a b : ℝ) :
    -pairQ a b 1 0 ≤ -(2 / 7 : ℝ) := by
  norm_num [pairQ]

/-- Generic B200 scalar response: normalized negative depth at least `c*T`
transfers to soft resolvent response at least `c/(1+c)`. -/
theorem soft_response_of_margin
    {T y c : ℝ}
    (hT : 0 < T)
    (hc : 0 < c)
    (hy : c * T ≤ y) :
    c / (1 + c) ≤ y / (T + y) := by
  have hypos : 0 < y := lt_of_lt_of_le (mul_pos hc hT) hy
  have hcden : 0 < 1 + c := by linarith
  have hyden : 0 < T + y := add_pos hT hypos
  apply (div_le_div_iff₀ hcden hyden).2
  nlinarith

/-- B200 scalar response: depth at least `(2/7)T` gives soft resolvent mass at
least `2/9`. -/
theorem soft_response_of_two_sevenths_margin
    {T y : ℝ}
    (hT : 0 < T)
    (hy : (2 / 7 : ℝ) * T ≤ y) :
    (2 / 9 : ℝ) ≤ y / (T + y) := by
  have h := soft_response_of_margin (T := T) (y := y) (c := (2 / 7 : ℝ))
    hT (by norm_num) hy
  norm_num at h ⊢
  exact h

#print axioms normalized_height_half
#print axioms pairQ_witness
#print axioms entering_pair_margin
#print axioms entering_pair_margin_kappa
#print axioms coeffQ_witness
#print axioms coefficient_only_entering_margin
#print axioms leaving_pair_margin
#print axioms soft_response_of_margin
#print axioms soft_response_of_two_sevenths_margin

end RHB202BGSTCrossingMarginFinite
