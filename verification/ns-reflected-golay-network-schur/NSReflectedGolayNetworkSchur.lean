import Mathlib

namespace B4NSReflectedGolayNetworkSchur

/-- Exact decomposition of a reflected symbol pair into constant, slope-mismatch, and remainder pieces. -/
theorem reflected_pair_first_jet_identity
    (c ellPlus ellMinus m rPlus rMinus w : ℝ) :
    (c + ellPlus * m + rPlus) * w +
        (c - ellMinus * m + rMinus) * w =
      2 * c * w + (ellPlus - ellMinus) * m * w +
        (rPlus + rMinus) * w := by
  ring

/-- Matched reflected slopes cancel the entire linear midpoint term exactly. -/
theorem matched_slope_first_jet_identity
    (c ell m rPlus rMinus w : ℝ) :
    (c + ell * m + rPlus) * w +
        (c - ell * m + rMinus) * w =
      2 * c * w + (rPlus + rMinus) * w := by
  ring

/-- With no Taylor remainder, one reflected pair retains only twice the constant symbol. -/
theorem exact_affine_pair_cancellation (c ell m w : ℝ) :
    (c + ell * m) * w + (c - ell * m) * w = 2 * c * w := by
  ring

/-- Reflection cancels arbitrary cell-dependent affine slopes over any finite family. -/
theorem reflected_affine_family_sum
    {ι : Type*} (s : Finset ι)
    (w m ell : ι → ℝ) (c : ℝ) :
    s.sum (fun i =>
        (c + ell i * m i) * w i + (c - ell i * m i) * w i) =
      2 * c * s.sum w := by
  calc
    s.sum (fun i =>
        (c + ell i * m i) * w i + (c - ell i * m i) * w i)
        = s.sum (fun i => 2 * c * w i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = 2 * c * s.sum w := by
      rw [Finset.mul_sum]

/-- A complementary family of reflected pairs cancels every common affine midpoint symbol. -/
theorem reflected_affine_complementary_cancel
    {σ ι : Type*} (species : Finset σ) (cells : Finset ι)
    (w m : σ → ι → ℝ) (ell : σ → ι → ℝ) (c : ℝ)
    (hcomp : species.sum (fun a => cells.sum (w a)) = 0) :
    species.sum (fun a =>
        cells.sum (fun i =>
          (c + ell a i * m a i) * w a i +
            (c - ell a i * m a i) * w a i)) = 0 := by
  calc
    species.sum (fun a =>
        cells.sum (fun i =>
          (c + ell a i * m a i) * w a i +
            (c - ell a i * m a i) * w a i))
        = species.sum (fun a => 2 * c * cells.sum (w a)) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact reflected_affine_family_sum cells (w a) (m a) (ell a) c
    _ = 2 * c * species.sum (fun a => cells.sum (w a)) := by
      rw [Finset.mul_sum]
    _ = 0 := by
      rw [hcomp, mul_zero]

/-- The two reflected Taylor remainders cost at most twice the per-copy error times the pair weight. -/
theorem reflected_pair_remainder_bound
    (rPlus rMinus w delta : ℝ)
    (hrPlus : |rPlus| ≤ delta) (hrMinus : |rMinus| ≤ delta) :
    |(rPlus + rMinus) * w| ≤ 2 * delta * |w| := by
  have hsum : |rPlus + rMinus| ≤ 2 * delta := by
    calc
      |rPlus + rMinus| ≤ |rPlus| + |rMinus| := abs_add rPlus rMinus
      _ ≤ delta + delta := add_le_add hrPlus hrMinus
      _ = 2 * delta := by ring
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right hsum (abs_nonneg w)

/-- Grouping all collisions by output frequency preserves the exact damped total-energy identity. -/
theorem damped_network_energy_identity
    {ι : Type*} (s : Finset ι) (z forcing gamma : ι → ℝ) :
    s.sum (fun i =>
        -2 * z i * forcing i +
          2 * z i * (forcing i - gamma i * z i)) =
      -2 * s.sum (fun i => gamma i * (z i) ^ 2) := by
  calc
    s.sum (fun i =>
        -2 * z i * forcing i +
          2 * z i * (forcing i - gamma i * z i))
        = s.sum (fun i => -2 * (gamma i * (z i) ^ 2)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = -2 * s.sum (fun i => gamma i * (z i) ^ 2) := by
      rw [Finset.mul_sum]

/-- Frozen elimination of every diagonal damped output gives the exact network Schur complement. -/
theorem diagonal_network_schur_identity
    {ι : Type*} (s : Finset ι) (forcing gamma : ι → ℝ) :
    s.sum (fun i => -2 * (forcing i / gamma i) * forcing i) =
      -2 * s.sum (fun i => (forcing i) ^ 2 / gamma i) := by
  calc
    s.sum (fun i => -2 * (forcing i / gamma i) * forcing i)
        = s.sum (fun i => -2 * ((forcing i) ^ 2 / gamma i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = -2 * s.sum (fun i => (forcing i) ^ 2 / gamma i) := by
      rw [Finset.mul_sum]

/-- Positive diagonal damping makes the frozen network Schur form nonpositive. -/
theorem diagonal_network_schur_nonpositive
    {ι : Type*} (s : Finset ι) (forcing gamma : ι → ℝ)
    (hgamma : ∀ i ∈ s, 0 < gamma i) :
    -2 * s.sum (fun i => (forcing i) ^ 2 / gamma i) ≤ 0 := by
  have hsum : 0 ≤ s.sum (fun i => (forcing i) ^ 2 / gamma i) := by
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (sq_nonneg (forcing i)) (le_of_lt (hgamma i hi))
  nlinarith

/-- Therefore the frozen active-energy correction of the whole grouped network is nonpositive. -/
theorem diagonal_network_active_correction_nonpositive
    {ι : Type*} (s : Finset ι) (forcing gamma : ι → ℝ)
    (hgamma : ∀ i ∈ s, 0 < gamma i) :
    s.sum (fun i => -2 * (forcing i / gamma i) * forcing i) ≤ 0 := by
  rw [diagonal_network_schur_identity]
  exact diagonal_network_schur_nonpositive s forcing gamma hgamma

#print axioms reflected_pair_first_jet_identity
#print axioms matched_slope_first_jet_identity
#print axioms exact_affine_pair_cancellation
#print axioms reflected_affine_family_sum
#print axioms reflected_affine_complementary_cancel
#print axioms reflected_pair_remainder_bound
#print axioms damped_network_energy_identity
#print axioms diagonal_network_schur_identity
#print axioms diagonal_network_schur_nonpositive
#print axioms diagonal_network_active_correction_nonpositive

end B4NSReflectedGolayNetworkSchur
