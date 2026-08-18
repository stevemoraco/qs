import Mathlib

namespace Millennium.RH

noncomputable def run10bnAlpha : ℝ := 214461 / 12765925
noncomputable def run10bnBeta : ℝ := 1833 / 1865
noncomputable def run10bnRB : ℝ := 12545052 / 12765925
noncomputable def run10bnRC : ℝ := 344 / 1865

noncomputable def run10bnField (A B C : ℝ) : ℝ :=
  run10bnAlpha * A + run10bnRB * B + run10bnRC * C

noncomputable def run10bnRoot (A B C : ℝ) : ℝ :=
  1 + (104 / 171 : ℝ) * A * B + (104 / 171 : ℝ) * A +
    (56 / 57 : ℝ) * B + (31 / 171 : ℝ) * C

noncomputable def run10bnWitness (A B C : ℝ) : ℝ :=
  ((101 / 100 : ℝ) - run10bnField A B C) * run10bnRoot A B C ^ 2

noncomputable def run10bnAvg8
    (f : ℝ → ℝ → ℝ → ℝ) (A B C : ℝ) : ℝ :=
  (f A B C + f A B (-C) + f A (-B) C + f A (-B) (-C) +
    f (-A) B C + f (-A) B (-C) + f (-A) (-B) C +
    f (-A) (-B) (-C)) / 8

noncomputable def run10bnEvenCore (A B C : ℝ) : ℝ :=
  (101 / 100 : ℝ)
    + (5273162336 / 14931536517 : ℝ) * A ^ 2
    - (7930666352 / 8295298065 : ℝ) * B ^ 2
    - (36738007 / 1090689300 : ℝ) * C ^ 2
    - (5576467312 / 14931536517 : ℝ) * A ^ 2 * B ^ 2

theorem run10bn_inner_pythagorean :
    run10bnAlpha ^ 2 + run10bnRB ^ 2 = run10bnBeta ^ 2 := by
  unfold run10bnAlpha run10bnRB run10bnBeta
  norm_num

theorem run10bn_outer_pythagorean :
    run10bnBeta ^ 2 + run10bnRC ^ 2 = 1 := by
  unfold run10bnBeta run10bnRC
  norm_num

theorem run10bn_root_support :
    run10bnAlpha + run10bnBeta = (12761346 / 12765925 : ℝ) ∧
    run10bnAlpha + run10bnBeta < 1 ∧
    1 - run10bnAlpha - run10bnBeta = (4579 / 12765925 : ℝ) := by
  unfold run10bnAlpha run10bnBeta
  norm_num

theorem run10bn_split_determinant_crosses :
    ((101 / 100 : ℝ) ^ 2 - 1) *
        ((101 / 100 : ℝ) ^ 2 - run10bnBeta ^ 2) <
      4 * run10bnAlpha ^ 2 * run10bnRB ^ 2 := by
  unfold run10bnAlpha run10bnBeta run10bnRB
  norm_num

theorem run10bn_cap_nonnegative
    (A B C : ℝ)
    (hcap : run10bnField A B C ≤ (101 / 100 : ℝ)) :
    0 ≤ run10bnWitness A B C := by
  unfold run10bnWitness
  exact mul_nonneg (sub_nonneg.mpr hcap) (sq_nonneg (run10bnRoot A B C))

theorem run10bn_sign_average_exact (A B C : ℝ) :
    run10bnAvg8 run10bnWitness A B C = run10bnEvenCore A B C := by
  unfold run10bnAvg8 run10bnWitness run10bnField run10bnRoot
    run10bnEvenCore run10bnAlpha run10bnRB run10bnRC
  ring

theorem run10bn_ideal_mass :
    (1 : ℝ)
      + (104 / 171 : ℝ) ^ 2
      + (104 / 171 : ℝ) ^ 2
      + (56 / 57 : ℝ) ^ 2
      + (31 / 171 : ℝ) ^ 2 =
        26686 / 9747 := by
  norm_num

theorem run10bn_ideal_numerator :
    2 *
      (run10bnAlpha * (104 / 171 : ℝ)
       + run10bnRB * (56 / 57 : ℝ)
       + run10bnRC * (31 / 171 : ℝ)
       + (104 / 171 : ℝ) *
          (run10bnRB * (104 / 171 : ℝ)
           + run10bnAlpha * (56 / 57 : ℝ))) =
      344083154656 / 124429470975 := by
  unfold run10bnAlpha run10bnRB run10bnRC
  norm_num

theorem run10bn_ideal_tilt_crosses :
    (172041577328 / 170335737275 : ℝ) > 101 / 100 := by
  norm_num

theorem run10bn_ideal_cap_mean :
    (101 / 100 : ℝ) * (26686 / 9747 : ℝ)
      - (344083154656 / 124429470975 : ℝ) =
        -(9930721 / 248858941950 : ℝ) := by
  norm_num

theorem run10bn_ideal_cap_mean_negative :
    -(9930721 / 248858941950 : ℝ) < 0 := by
  norm_num

theorem run10bn_worst_signed_height :
    1 + 2 * run10bnAlpha = (13194847 / 12765925 : ℝ) := by
  unfold run10bnAlpha
  norm_num

theorem run10bn_worst_signed_height_supernatural :
    (1 : ℝ) < 1 + 2 * run10bnAlpha := by
  unfold run10bnAlpha
  norm_num

theorem run10bn_A2B2C_height_order :
    1 + 2 * run10bnAlpha < 2 * run10bnBeta := by
  unfold run10bnAlpha run10bnBeta
  norm_num

theorem run10bn_top_support_ledger :
    run10bnAlpha + run10bnBeta = (12761346 / 12765925 : ℝ) ∧
    run10bnBeta + 2 * run10bnAlpha = (12975807 / 12765925 : ℝ) ∧
    1 + run10bnAlpha = (12980386 / 12765925 : ℝ) ∧
    1 + 2 * run10bnAlpha = (13194847 / 12765925 : ℝ) := by
  unfold run10bnAlpha run10bnBeta
  norm_num

#print axioms run10bn_inner_pythagorean
#print axioms run10bn_outer_pythagorean
#print axioms run10bn_root_support
#print axioms run10bn_split_determinant_crosses
#print axioms run10bn_cap_nonnegative
#print axioms run10bn_sign_average_exact
#print axioms run10bn_ideal_mass
#print axioms run10bn_ideal_numerator
#print axioms run10bn_ideal_tilt_crosses
#print axioms run10bn_ideal_cap_mean
#print axioms run10bn_ideal_cap_mean_negative
#print axioms run10bn_worst_signed_height
#print axioms run10bn_worst_signed_height_supernatural
#print axioms run10bn_A2B2C_height_order
#print axioms run10bn_top_support_ledger

end Millennium.RH
