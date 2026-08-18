import Mathlib

namespace Millennium.RH

/--
The ideal Run10 split-shell mass of one affine square
`(c + alpha*A + beta*B)^2` under

`E A = E B = E(AB) = 0`,
`E A^2 = 1/4`, `E B^2 = 3/4`.

The probability/Bohr interpretation is deliberately external; this file
formalizes only the exact scalar consumer.
-/
noncomputable def run10bgMass (c alpha beta : ℝ) : ℝ :=
  c ^ 2 + alpha ^ 2 / 4 + 3 * beta ^ 2 / 4

/--
The corresponding ideal `Y=A+B` weighted numerator when all centered cubic
moments appearing in the expansion vanish.
-/
noncomputable def run10bgYNumerator (c alpha beta : ℝ) : ℝ :=
  c * (alpha + 3 * beta) / 2

/--
Exact square-completion identity behind the degree-three cap-localizer
firewall.
-/
theorem run10bg_affine_square_gap_identity (c alpha beta : ℝ) :
    run10bgMass c alpha beta - run10bgYNumerator c alpha beta =
      (c - (alpha + 3 * beta) / 4) ^ 2 +
        3 * (alpha - beta) ^ 2 / 16 := by
  unfold run10bgMass run10bgYNumerator
  ring

/-- The ideal affine-square mass is nonnegative. -/
theorem run10bg_mass_nonneg (c alpha beta : ℝ) :
    0 ≤ run10bgMass c alpha beta := by
  unfold run10bgMass
  positivity

/-- The completed-square gap is nonnegative. -/
theorem run10bg_affine_square_gap_nonneg (c alpha beta : ℝ) :
    0 ≤ run10bgMass c alpha beta - run10bgYNumerator c alpha beta := by
  rw [run10bg_affine_square_gap_identity]
  positivity

/--
At the unit threshold, no affine-square localizer can tilt the ideal split
shell to a `Y`-mean above one.
-/
theorem run10bg_numerator_le_mass (c alpha beta : ℝ) :
    run10bgYNumerator c alpha beta ≤ run10bgMass c alpha beta := by
  exact sub_nonneg.mp (run10bg_affine_square_gap_nonneg c alpha beta)

/--
For every threshold `q ≥ 1`, a cap witness of the form
`(q-Y) * (c+alpha*A+beta*B)^2` has nonnegative ideal mean.
-/
theorem run10bg_affine_square_threshold_barrier
    (q c alpha beta : ℝ) (hq : 1 ≤ q) :
    0 ≤ q * run10bgMass c alpha beta -
      run10bgYNumerator c alpha beta := by
  calc
    q * run10bgMass c alpha beta - run10bgYNumerator c alpha beta =
        (q - 1) * run10bgMass c alpha beta +
          (run10bgMass c alpha beta - run10bgYNumerator c alpha beta) := by
            ring
    _ ≥ 0 := add_nonneg
      (mul_nonneg (sub_nonneg.mpr hq) (run10bg_mass_nonneg c alpha beta))
      (run10bg_affine_square_gap_nonneg c alpha beta)

/--
The same barrier survives every finite nonnegative sum of affine squares,
which is the finite SOS form used by a globally nonnegative quadratic
localizer.
-/
theorem run10bg_finite_sos_threshold_barrier
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (weight c alpha beta : ι → ℝ)
    (q : ℝ)
    (hq : 1 ≤ q)
    (hw : ∀ i ∈ s, 0 ≤ weight i) :
    0 ≤ ∑ i ∈ s, weight i *
      (q * run10bgMass (c i) (alpha i) (beta i) -
        run10bgYNumerator (c i) (alpha i) (beta i)) := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i hi)
    (run10bg_affine_square_threshold_barrier
      q (c i) (alpha i) (beta i) hq)

/--
The constant `1` is sharp: along the equality direction
`c=alpha=beta=t`, the ideal weighted numerator equals the mass exactly.
-/
theorem run10bg_unit_threshold_sharp (t : ℝ) :
    run10bgMass t t t = run10bgYNumerator t t t := by
  unfold run10bgMass run10bgYNumerator
  ring

/--
Run10be's quartic localizer escapes the quadratic/SOS barrier at the target
`q=101/100`: its ideal degree-five cap witness has strictly negative mean.
This is only the exact rational terminal arithmetic already exposed by the
parent branch; no natural-window transfer is encoded here.
-/
theorem run10bg_run10be_degree_five_negative :
    (101 / 100 : ℝ) * (35 / 16 : ℝ) - (11 / 4 : ℝ) < 0 := by
  norm_num

#print axioms run10bg_affine_square_gap_identity
#print axioms run10bg_mass_nonneg
#print axioms run10bg_affine_square_gap_nonneg
#print axioms run10bg_numerator_le_mass
#print axioms run10bg_affine_square_threshold_barrier
#print axioms run10bg_finite_sos_threshold_barrier
#print axioms run10bg_unit_threshold_sharp
#print axioms run10bg_run10be_degree_five_negative

end Millennium.RH
