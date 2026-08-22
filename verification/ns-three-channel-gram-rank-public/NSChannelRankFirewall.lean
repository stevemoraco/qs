import Mathlib

namespace NSChannelRank

/-- Three vectors in a two-dimensional channel plane have a singular Gram
matrix.  This is the exact rank-two polynomial identity, written in coordinates
so that no dimension or rank bridge is hidden. -/
theorem three_channel_gram_determinant_zero
    (a0 b0 a1 b1 a2 b2 : ℝ) :
    (a0 ^ 2 + b0 ^ 2) * (a1 ^ 2 + b1 ^ 2) * (a2 ^ 2 + b2 ^ 2)
        + 2 * (a0 * a1 + b0 * b1) * (a0 * a2 + b0 * b2)
            * (a1 * a2 + b1 * b2)
        - (a0 ^ 2 + b0 ^ 2) * (a1 * a2 + b1 * b2) ^ 2
        - (a1 ^ 2 + b1 ^ 2) * (a0 * a2 + b0 * b2) ^ 2
        - (a2 ^ 2 + b2 ^ 2) * (a0 * a1 + b0 * b1) ^ 2
      = 0 := by
  ring

/-- Exact weighted frame-potential identity for three unit channels in a
two-dimensional polarization plane.  The first term on the right is the
dimension-two Welch floor; the final two squares are the anisotropy remainder.
Positive weights are not needed for the algebraic identity, though they are
needed for the Navier--Stokes channel interpretation. -/
theorem three_channel_weighted_frame_identity
    (w0 w1 w2 a0 b0 a1 b1 a2 b2 : ℝ)
    (h0 : a0 ^ 2 + b0 ^ 2 = 1)
    (h1 : a1 ^ 2 + b1 ^ 2 = 1)
    (h2 : a2 ^ 2 + b2 ^ 2 = 1) :
    w0 * w1 * (a0 * a1 + b0 * b1) ^ 2
        + w0 * w2 * (a0 * a2 + b0 * b2) ^ 2
        + w1 * w2 * (a1 * a2 + b1 * b2) ^ 2
      =
        ((w0 + w1 + w2) ^ 2 - 2 * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2)) / 4
          + (w0 * (a0 ^ 2 - b0 ^ 2) + w1 * (a1 ^ 2 - b1 ^ 2)
              + w2 * (a2 ^ 2 - b2 ^ 2)) ^ 2 / 4
          + (w0 * a0 * b0 + w1 * a1 * b1 + w2 * a2 * b2) ^ 2 := by
  let A : ℝ := w0 * a0 ^ 2 + w1 * a1 ^ 2 + w2 * a2 ^ 2
  let B : ℝ := w0 * b0 ^ 2 + w1 * b1 ^ 2 + w2 * b2 ^ 2
  let D : ℝ := w0 * a0 * b0 + w1 * a1 * b1 + w2 * a2 * b2
  let P : ℝ :=
    w0 * w1 * (a0 * a1 + b0 * b1) ^ 2
      + w0 * w2 * (a0 * a2 + b0 * b2) ^ 2
      + w1 * w2 * (a1 * a2 + b1 * b2) ^ 2
  let W : ℝ := w0 + w1 + w2
  let Q : ℝ := w0 ^ 2 + w1 ^ 2 + w2 ^ 2
  have hframe : A ^ 2 + B ^ 2 + 2 * D ^ 2 = Q + 2 * P := by
    dsimp [A, B, D, Q, P]
    calc
      (w0 * a0 ^ 2 + w1 * a1 ^ 2 + w2 * a2 ^ 2) ^ 2
          + (w0 * b0 ^ 2 + w1 * b1 ^ 2 + w2 * b2 ^ 2) ^ 2
          + 2 * (w0 * a0 * b0 + w1 * a1 * b1 + w2 * a2 * b2) ^ 2
        =
          w0 ^ 2 * (a0 ^ 2 + b0 ^ 2) ^ 2
            + w1 ^ 2 * (a1 ^ 2 + b1 ^ 2) ^ 2
            + w2 ^ 2 * (a2 ^ 2 + b2 ^ 2) ^ 2
            + 2 *
              (w0 * w1 * (a0 * a1 + b0 * b1) ^ 2
                + w0 * w2 * (a0 * a2 + b0 * b2) ^ 2
                + w1 * w2 * (a1 * a2 + b1 * b2) ^ 2) := by
              ring
      _ =
          (w0 ^ 2 + w1 ^ 2 + w2 ^ 2)
            + 2 *
              (w0 * w1 * (a0 * a1 + b0 * b1) ^ 2
                + w0 * w2 * (a0 * a2 + b0 * b2) ^ 2
                + w1 * w2 * (a1 * a2 + b1 * b2) ^ 2) := by
              rw [h0, h1, h2]
              ring
  have htrace : A + B = W := by
    dsimp [A, B, W]
    calc
      (w0 * a0 ^ 2 + w1 * a1 ^ 2 + w2 * a2 ^ 2)
          + (w0 * b0 ^ 2 + w1 * b1 ^ 2 + w2 * b2 ^ 2)
        =
          w0 * (a0 ^ 2 + b0 ^ 2)
            + w1 * (a1 ^ 2 + b1 ^ 2)
            + w2 * (a2 ^ 2 + b2 ^ 2) := by
              ring
      _ = w0 + w1 + w2 := by
              rw [h0, h1, h2]
              ring
  have hid :
      P = ((A + B) ^ 2 - 2 * Q) / 4 + (A - B) ^ 2 / 4 + D ^ 2 := by
    nlinarith [hframe]
  have hmain :
      P = (W ^ 2 - 2 * Q) / 4 + (A - B) ^ 2 / 4 + D ^ 2 := by
    calc
      P = ((A + B) ^ 2 - 2 * Q) / 4 + (A - B) ^ 2 / 4 + D ^ 2 := hid
      _ = (W ^ 2 - 2 * Q) / 4 + (A - B) ^ 2 / 4 + D ^ 2 := by rw [htrace]
  dsimp [P, W, Q, A, B, D] at hmain
  convert hmain using 1 <;> ring

/-- Three unit channel directions in a real two-dimensional plane have total
squared pair-correlation at least `3/4`. -/
theorem three_unit_channels_welch_floor
    (a0 b0 a1 b1 a2 b2 : ℝ)
    (h0 : a0 ^ 2 + b0 ^ 2 = 1)
    (h1 : a1 ^ 2 + b1 ^ 2 = 1)
    (h2 : a2 ^ 2 + b2 ^ 2 = 1) :
    (3 : ℝ) / 4
      ≤ (a0 * a1 + b0 * b1) ^ 2
          + (a0 * a2 + b0 * b2) ^ 2
          + (a1 * a2 + b1 * b2) ^ 2 := by
  have hid :=
    three_channel_weighted_frame_identity
      1 1 1 a0 b0 a1 b1 a2 b2 h0 h1 h2
  norm_num at hid
  nlinarith [
    sq_nonneg
      ((a0 ^ 2 - b0 ^ 2) + (a1 ^ 2 - b1 ^ 2) + (a2 ^ 2 - b2 ^ 2)),
    sq_nonneg (a0 * b0 + a1 * b1 + a2 * b2)
  ]

/-- Therefore three nonzero normalized channels in one divergence-free
polarization plane cannot be pairwise weakly correlated: some pair has squared
correlation at least `1/4`, equivalently absolute correlation at least `1/2`. -/
theorem three_unit_channels_have_half_coherent_pair
    (a0 b0 a1 b1 a2 b2 : ℝ)
    (h0 : a0 ^ 2 + b0 ^ 2 = 1)
    (h1 : a1 ^ 2 + b1 ^ 2 = 1)
    (h2 : a2 ^ 2 + b2 ^ 2 = 1) :
    (1 : ℝ) / 4 ≤ (a0 * a1 + b0 * b1) ^ 2
      ∨ (1 : ℝ) / 4 ≤ (a0 * a2 + b0 * b2) ^ 2
      ∨ (1 : ℝ) / 4 ≤ (a1 * a2 + b1 * b2) ^ 2 := by
  have hsum :=
    three_unit_channels_welch_floor a0 b0 a1 b1 a2 b2 h0 h1 h2
  by_contra h
  push_neg at h
  nlinarith

/-- The threshold is sharp at the correlation-data level: three pairwise
correlations all equal to `-1/2` saturate both the Gram determinant relation and
the Welch floor.  The standard `120°` unit frame realizes these data. -/
theorem half_coherence_threshold_scalar_sharp :
    1 + 2 * ((-1 : ℝ) / 2) * ((-1 : ℝ) / 2) * ((-1 : ℝ) / 2)
          - ((-1 : ℝ) / 2) ^ 2 - ((-1 : ℝ) / 2) ^ 2
          - ((-1 : ℝ) / 2) ^ 2 = 0
      ∧ ((-1 : ℝ) / 2) ^ 2 + ((-1 : ℝ) / 2) ^ 2
          + ((-1 : ℝ) / 2) ^ 2 = (3 : ℝ) / 4 := by
  norm_num

#print axioms three_channel_gram_determinant_zero
#print axioms three_channel_weighted_frame_identity
#print axioms three_unit_channels_welch_floor
#print axioms three_unit_channels_have_half_coherent_pair
#print axioms half_coherence_threshold_scalar_sharp

end NSChannelRank
