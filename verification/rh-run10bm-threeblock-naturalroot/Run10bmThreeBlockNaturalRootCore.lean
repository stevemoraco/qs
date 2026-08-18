import Mathlib

namespace Millennium.RH

/-- Equal average over all eight independent sign flips of three real variables. -/
noncomputable def run10bmAvg8
    (f : ℝ → ℝ → ℝ → ℝ) (A B C : ℝ) : ℝ :=
  (f A B C + f A B (-C) + f A (-B) C + f A (-B) (-C) +
    f (-A) B C + f (-A) B (-C) + f (-A) (-B) C +
    f (-A) (-B) (-C)) / 8

/-- Three-block quadratic root. Its only quadratic cross term is `A*B`. -/
noncomputable def run10bmRoot (A B C : ℝ) : ℝ :=
  1 + (5 / 3 : ℝ) * A + (5 / 4 : ℝ) * B + (7 / 8 : ℝ) * C +
    (125 / 54 : ℝ) * A * B

/-- Degree-five cap witness at the literal `101/100` threshold. -/
noncomputable def run10bmWitness (A B C : ℝ) : ℝ :=
  ((101 / 100 : ℝ) - A - B - C) * run10bmRoot A B C ^ 2

/-- The exact separately-even part of the three-block witness. -/
noncomputable def run10bmEvenCore (A B C : ℝ) : ℝ :=
  (101 / 100 : ℝ)
    - (19 / 36 : ℝ) * A ^ 2
    - (59 / 64 : ℝ) * B ^ 2
    - (6251 / 6400 : ℝ) * C ^ 2
    - (94375 / 11664 : ℝ) * A ^ 2 * B ^ 2

/-- The cap witness is pointwise nonnegative whenever the actual three-block
sum lies below the cap. -/
theorem run10bm_cap_nonnegative
    (A B C : ℝ)
    (hcap : A + B + C ≤ (101 / 100 : ℝ)) :
    0 ≤ run10bmWitness A B C := by
  unfold run10bmWitness
  have hfactor : 0 ≤ (101 / 100 : ℝ) - A - B - C := by
    linarith
  exact mul_nonneg hfactor (sq_nonneg (run10bmRoot A B C))

/-- Averaging over the eight independent sign flips removes exactly the
orientation sector and leaves the stated even core. -/
theorem run10bm_sign_average_exact (A B C : ℝ) :
    run10bmAvg8 run10bmWitness A B C = run10bmEvenCore A B C := by
  unfold run10bmAvg8 run10bmWitness run10bmRoot run10bmEvenCore
  ring

/-- Exact PNT variance ledger for exponent cuts `9/25`, `3/5`, and `1`. -/
theorem run10bm_variance_ledger :
    (81 / 625 : ℝ) + (144 / 625 : ℝ) + (16 / 25 : ℝ) = 1 := by
  norm_num

/-- The unique quadratic root cross term has multiplicative exponent `24/25`. -/
theorem run10bm_AB_support_exponent :
    (9 / 25 : ℝ) + (3 / 5 : ℝ) = 24 / 25 := by
  norm_num

/-- The root cross term has a strict natural-window exponent reserve. -/
theorem run10bm_AB_support_strictly_natural :
    (24 / 25 : ℝ) < 1 := by
  norm_num

/-- Substituting the exact variance targets and factorized `A^2 B^2` target
into the even core gives the exact negative margin `-11/80`. -/
theorem run10bm_ideal_even_margin :
    (101 / 100 : ℝ)
      - (19 / 36 : ℝ) * (81 / 625 : ℝ)
      - (59 / 64 : ℝ) * (144 / 625 : ℝ)
      - (6251 / 6400 : ℝ) * (16 / 25 : ℝ)
      - (94375 / 11664 : ℝ) *
          ((81 / 625 : ℝ) * (144 / 625 : ℝ)) =
        -(11 / 80 : ℝ) := by
  norm_num

/-- Exact ideal mass of the square localizer in the independent sign model. -/
theorem run10bm_ideal_mass :
    (237 / 100 : ℝ) > 0 := by
  norm_num

/-- Exact ideal weighted numerator. -/
theorem run10bm_ideal_numerator :
    (1582 / 625 : ℝ) > 0 := by
  norm_num

/-- Exact ideal tilt ratio. -/
theorem run10bm_ideal_tilt_ratio :
    (1582 / 625 : ℝ) / (237 / 100 : ℝ) = 6328 / 5925 := by
  norm_num

/-- The ideal tilt crosses the literal `101/100` Suzuki cap. -/
theorem run10bm_ideal_tilt_crosses_cap :
    (101 / 100 : ℝ) < (6328 / 5925 : ℝ) := by
  norm_num

/-- The mass/numerator form has the same exact `-11/80` witness margin. -/
theorem run10bm_mass_numerator_margin :
    (101 / 100 : ℝ) * (237 / 100 : ℝ) - (1582 / 625 : ℝ) =
      -(11 / 80 : ℝ) := by
  norm_num

/-- Denominator-free robust error consumer for the four unconditional even
moment rows. -/
theorem run10bm_even_error_budget
    (dA dB dC dAB : ℝ)
    (hbudget :
      (19 / 36 : ℝ) * dA +
        (59 / 64 : ℝ) * dB +
        (6251 / 6400 : ℝ) * dC +
        (94375 / 11664 : ℝ) * dAB < 11 / 80) :
    -(11 / 80 : ℝ) +
        (19 / 36 : ℝ) * dA +
        (59 / 64 : ℝ) * dB +
        (6251 / 6400 : ℝ) * dC +
        (94375 / 11664 : ℝ) * dAB < 0 := by
  linarith

/-- Exact top-degree signed remainder produced by the unique quadratic root
term. This is the degree-five orientation row that the finite core does not
estimate on the physical prime window. -/
noncomputable def run10bmTopOdd (A B C : ℝ) : ℝ :=
  -(15625 / 2916 : ℝ) *
    (A ^ 3 * B ^ 2 + A ^ 2 * B ^ 3 + A ^ 2 * B ^ 2 * C)

/-- The displayed top-degree row factors through `A^2 B^2 (A+B+C)`. -/
theorem run10bm_top_odd_factorization (A B C : ℝ) :
    run10bmTopOdd A B C =
      -(15625 / 2916 : ℝ) * A ^ 2 * B ^ 2 * (A + B + C) := by
  unfold run10bmTopOdd
  ring

#check run10bmAvg8
#check run10bmRoot
#check run10bmWitness
#check run10bmEvenCore
#check run10bm_cap_nonnegative
#print axioms run10bm_cap_nonnegative
#check run10bm_sign_average_exact
#print axioms run10bm_sign_average_exact
#check run10bm_variance_ledger
#print axioms run10bm_variance_ledger
#check run10bm_AB_support_exponent
#print axioms run10bm_AB_support_exponent
#check run10bm_AB_support_strictly_natural
#print axioms run10bm_AB_support_strictly_natural
#check run10bm_ideal_even_margin
#print axioms run10bm_ideal_even_margin
#check run10bm_ideal_mass
#print axioms run10bm_ideal_mass
#check run10bm_ideal_numerator
#print axioms run10bm_ideal_numerator
#check run10bm_ideal_tilt_ratio
#print axioms run10bm_ideal_tilt_ratio
#check run10bm_ideal_tilt_crosses_cap
#print axioms run10bm_ideal_tilt_crosses_cap
#check run10bm_mass_numerator_margin
#print axioms run10bm_mass_numerator_margin
#check run10bm_even_error_budget
#print axioms run10bm_even_error_budget
#check run10bmTopOdd
#check run10bm_top_odd_factorization
#print axioms run10bm_top_odd_factorization

end Millennium.RH
