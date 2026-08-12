import Mathlib

namespace NSGolayIntermittencyDuality

/-- The pointwise squared power of eight tensor-product species factors into
the three one-dimensional pair powers. -/
theorem tensor_eight_species_power_factorization
    (a0 a1 b0 b1 c0 c1 : ℝ) :
    (a0 * b0 * c0) ^ 2 + (a0 * b0 * c1) ^ 2
      + (a0 * b1 * c0) ^ 2 + (a0 * b1 * c1) ^ 2
      + (a1 * b0 * c0) ^ 2 + (a1 * b0 * c1) ^ 2
      + (a1 * b1 * c0) ^ 2 + (a1 * b1 * c1) ^ 2
      =
    (a0 ^ 2 + a1 ^ 2) * (b0 ^ 2 + b1 ^ 2) * (c0 ^ 2 + c1 ^ 2) := by
  ring

/-- Pointwise complementary pair-power identities make the total power of the
eight tensor species exactly constant. -/
theorem tensor_complementary_power_flatness
    (a0 a1 b0 b1 c0 c1 EA EB EC : ℝ)
    (ha : a0 ^ 2 + a1 ^ 2 = EA)
    (hb : b0 ^ 2 + b1 ^ 2 = EB)
    (hc : c0 ^ 2 + c1 ^ 2 = EC) :
    (a0 * b0 * c0) ^ 2 + (a0 * b0 * c1) ^ 2
      + (a0 * b1 * c0) ^ 2 + (a0 * b1 * c1) ^ 2
      + (a1 * b0 * c0) ^ 2 + (a1 * b0 * c1) ^ 2
      + (a1 * b1 * c0) ^ 2 + (a1 * b1 * c1) ^ 2
      = EA * EB * EC := by
  calc
    (a0 * b0 * c0) ^ 2 + (a0 * b0 * c1) ^ 2
        + (a0 * b1 * c0) ^ 2 + (a0 * b1 * c1) ^ 2
        + (a1 * b0 * c0) ^ 2 + (a1 * b0 * c1) ^ 2
        + (a1 * b1 * c0) ^ 2 + (a1 * b1 * c1) ^ 2
        =
      (a0 ^ 2 + a1 ^ 2) * (b0 ^ 2 + b1 ^ 2) * (c0 ^ 2 + c1 ^ 2) :=
        tensor_eight_species_power_factorization a0 a1 b0 b1 c0 c1
    _ = EA * EB * EC := by rw [ha, hb, hc]

/-- Two coherent channels can improve amplitude by at most a factor `sqrt 2`
relative to their combined squared power. -/
theorem two_channel_coherent_cap (x y : ℝ) :
    (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y)]

/-- Eight coherent channels can improve squared amplitude by at most a factor
eight relative to their total squared power. -/
theorem eight_channel_coherent_cap
    (x0 x1 x2 x3 x4 x5 x6 x7 : ℝ) :
    (x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7) ^ 2
      ≤ 8 * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2
        + x4 ^ 2 + x5 ^ 2 + x6 ^ 2 + x7 ^ 2) := by
  have h01 := two_channel_coherent_cap x0 x1
  have h23 := two_channel_coherent_cap x2 x3
  have h45 := two_channel_coherent_cap x4 x5
  have h67 := two_channel_coherent_cap x6 x7
  have h0123 := two_channel_coherent_cap (x0 + x1) (x2 + x3)
  have h4567 := two_channel_coherent_cap (x4 + x5) (x6 + x7)
  have hall :=
    two_channel_coherent_cap (x0 + x1 + x2 + x3) (x4 + x5 + x6 + x7)
  nlinarith

/-- If eight fixed species have total pointwise power `E`, a claimed
`c * sqrt M` coherent gain forces `c^2 M ≤ 8`. Hence a fixed eight-species
complementary frame cannot support a growing intermittency ratio. -/
theorem fixed_eight_species_gain_ceiling
    (M c E y : ℝ)
    (hE : 0 < E)
    (hgain : c ^ 2 * M * E ≤ y ^ 2)
    (hcap : y ^ 2 ≤ 8 * E) :
    c ^ 2 * M ≤ 8 := by
  have hscaled : (c ^ 2 * M) * E ≤ 8 * E := by
    calc
      (c ^ 2 * M) * E = c ^ 2 * M * E := by ring
      _ ≤ y ^ 2 := hgain
      _ ≤ 8 * E := hcap
  exact le_of_mul_le_mul_right hscaled hE

/-- The tensor-product complementary power identities, together with coherent
addition of the eight species, give a mode-count-independent gain ceiling. -/
theorem tensor_complementarity_gain_ceiling
    (a0 a1 b0 b1 c0 c1 EA EB EC M c : ℝ)
    (ha : a0 ^ 2 + a1 ^ 2 = EA)
    (hb : b0 ^ 2 + b1 ^ 2 = EB)
    (hc : c0 ^ 2 + c1 ^ 2 = EC)
    (hE : 0 < EA * EB * EC)
    (hgain :
      c ^ 2 * M * (EA * EB * EC)
        ≤
      (a0 * b0 * c0 + a0 * b0 * c1
        + a0 * b1 * c0 + a0 * b1 * c1
        + a1 * b0 * c0 + a1 * b0 * c1
        + a1 * b1 * c0 + a1 * b1 * c1) ^ 2) :
    c ^ 2 * M ≤ 8 := by
  have hcoherent :=
    eight_channel_coherent_cap
      (a0 * b0 * c0) (a0 * b0 * c1)
      (a0 * b1 * c0) (a0 * b1 * c1)
      (a1 * b0 * c0) (a1 * b0 * c1)
      (a1 * b1 * c0) (a1 * b1 * c1)
  have hflat :=
    tensor_complementary_power_flatness
      a0 a1 b0 b1 c0 c1 EA EB EC ha hb hc
  have hcap :
      (a0 * b0 * c0 + a0 * b0 * c1
        + a0 * b1 * c0 + a0 * b1 * c1
        + a1 * b0 * c0 + a1 * b0 * c1
        + a1 * b1 * c0 + a1 * b1 * c1) ^ 2
        ≤ 8 * (EA * EB * EC) := by
    calc
      (a0 * b0 * c0 + a0 * b0 * c1
        + a0 * b1 * c0 + a0 * b1 * c1
        + a1 * b0 * c0 + a1 * b0 * c1
        + a1 * b1 * c0 + a1 * b1 * c1) ^ 2
        ≤
      8 * ((a0 * b0 * c0) ^ 2 + (a0 * b0 * c1) ^ 2
        + (a0 * b1 * c0) ^ 2 + (a0 * b1 * c1) ^ 2
        + (a1 * b0 * c0) ^ 2 + (a1 * b0 * c1) ^ 2
        + (a1 * b1 * c0) ^ 2 + (a1 * b1 * c1) ^ 2) := hcoherent
      _ = 8 * (EA * EB * EC) := by rw [hflat]
  exact fixed_eight_species_gain_ceiling
    M c (EA * EB * EC)
    (a0 * b0 * c0 + a0 * b0 * c1
      + a0 * b1 * c0 + a0 * b1 * c1
      + a1 * b0 * c0 + a1 * b0 * c1
      + a1 * b1 * c0 + a1 * b1 * c1)
    hE hgain hcap

#print axioms tensor_eight_species_power_factorization
#print axioms tensor_complementary_power_flatness
#print axioms two_channel_coherent_cap
#print axioms eight_channel_coherent_cap
#print axioms fixed_eight_species_gain_ceiling
#print axioms tensor_complementarity_gain_ceiling

end NSGolayIntermittencyDuality
