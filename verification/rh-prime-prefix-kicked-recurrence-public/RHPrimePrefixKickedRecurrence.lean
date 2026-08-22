import Mathlib

namespace RHPrimePrefixKickedRecurrence

/-- Abstract endpoint margin. In the RH application `u = sqrt p`,
`theta = ϑ(p)`, `A = ∑_{r≤p} log r / sqrt r`, and `c = sqrt 2`. -/
noncomputable def endpoint (u theta A c : ℝ) : ℝ :=
  u + theta / u - c - A

/-- The Chebyshev jump and weighted-prime-moment jump cancel at a prime arrival. -/
theorem arrival_jump_cancellation
    {v theta A c ell : ℝ}
    (hv : v ≠ 0) :
    endpoint v (theta + ell) (A + ell / v) c = endpoint v theta A c := by
  unfold endpoint
  field_simp [hv]
  ring

/-- Exact endpoint increment between two consecutive square-root coordinates. -/
theorem endpoint_increment_identity
    {u v theta A c : ℝ}
    (hu : u ≠ 0)
    (hv : v ≠ 0) :
    endpoint v theta A c - endpoint u theta A c =
      (v - u) * (1 - theta / (u * v)) := by
  unfold endpoint
  field_simp [hu, hv]
  ring

/-- Exact arrived-state recurrence after the new prime's two jumps cancel. -/
theorem arrived_endpoint_increment
    {u v theta A c ell : ℝ}
    (hu : u ≠ 0)
    (hv : v ≠ 0) :
    endpoint v (theta + ell) (A + ell / v) c - endpoint u theta A c =
      (v - u) * (1 - theta / (u * v)) := by
  rw [arrival_jump_cancellation hv]
  exact endpoint_increment_identity hu hv

/-- Below the geometric-mean threshold, a positive spacing cannot decrease the endpoint. -/
theorem endpoint_nondecreasing_of_below_geometric_threshold
    {u v theta A c : ℝ}
    (hu : 0 < u)
    (huv : u ≤ v)
    (htheta : theta ≤ u * v) :
    endpoint u theta A c ≤ endpoint v theta A c := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have huvpos : 0 < u * v := mul_pos hu hv
  have hratio : theta / (u * v) ≤ 1 := by
    exact (div_le_one huvpos).2 htheta
  have hfirst : 0 ≤ v - u := sub_nonneg.mpr huv
  have hsecond : 0 ≤ 1 - theta / (u * v) := sub_nonneg.mpr hratio
  have hprod : 0 ≤ (v - u) * (1 - theta / (u * v)) :=
    mul_nonneg hfirst hsecond
  have hid := endpoint_increment_identity
    (A := A) (c := c) (theta := theta) (u := u) (v := v)
    (hu := ne_of_gt hu) (hv := ne_of_gt hv)
  linarith

/-- Above the geometric-mean threshold, a strict positive spacing strictly decreases the endpoint. -/
theorem endpoint_decreases_of_above_geometric_threshold
    {u v theta A c : ℝ}
    (hu : 0 < u)
    (huv : u < v)
    (htheta : u * v < theta) :
    endpoint v theta A c < endpoint u theta A c := by
  have hv : 0 < v := lt_trans hu huv
  have huvpos : 0 < u * v := mul_pos hu hv
  have hratio : 1 < theta / (u * v) := by
    exact (lt_div_iff₀ huvpos).2 (by simpa using htheta)
  have hfirst : 0 < v - u := sub_pos.mpr huv
  have hsecond : 1 - theta / (u * v) < 0 := sub_neg.mpr hratio
  have hprod : (v - u) * (1 - theta / (u * v)) < 0 :=
    mul_neg_of_pos_of_neg hfirst hsecond
  have hid := endpoint_increment_identity
    (A := A) (c := c) (theta := theta) (u := u) (v := v)
    (hu := ne_of_gt hu) (hv := ne_of_gt hv)
  linarith

/-- With positive square-root coordinates, endpoint decrease is equivalent to crossing
`theta > u*v`. -/
theorem endpoint_decreases_iff_geometric_threshold
    {u v theta A c : ℝ}
    (hu : 0 < u)
    (huv : u < v) :
    endpoint v theta A c < endpoint u theta A c ↔ u * v < theta := by
  constructor
  · intro hdec
    by_contra hnot
    have htheta : theta ≤ u * v := le_of_not_gt hnot
    have hmono := endpoint_nondecreasing_of_below_geometric_threshold
      hu (le_of_lt huv) htheta (A := A) (c := c)
    linarith
  · intro htheta
    exact endpoint_decreases_of_above_geometric_threshold hu huv htheta

/-- Positive spacing alone does not force endpoint growth. -/
theorem positive_spacing_countermodel :
    endpoint (2 : ℝ) 3 0 0 < endpoint (1 : ℝ) 3 0 0 := by
  norm_num [endpoint]

/-- Exact surplus of the left endpoint over an interior critical value. -/
theorem left_endpoint_surplus_identity
    {u s A c : ℝ}
    (hu : u ≠ 0) :
    endpoint u (s ^ 2) A c - (2 * s - c - A) = (s - u) ^ 2 / u := by
  unfold endpoint
  field_simp [hu]
  ring

/-- Exact surplus of the right endpoint over the same interior critical value. -/
theorem right_endpoint_surplus_identity
    {v s A c : ℝ}
    (hv : v ≠ 0) :
    endpoint v (s ^ 2) A c - (2 * s - c - A) = (v - s) ^ 2 / v := by
  unfold endpoint
  field_simp [hv]
  ring

/-- The interior loss can be written exactly as a quadratic Chebyshev excess. -/
theorem quadratic_excess_identity
    {u s : ℝ}
    (hu : u ≠ 0)
    (hsum : s + u ≠ 0) :
    (s - u) ^ 2 / u =
      (s ^ 2 - u ^ 2) ^ 2 / (u * (s + u) ^ 2) := by
  field_simp [hu, hsum]
  ring

#print axioms arrival_jump_cancellation
#print axioms endpoint_increment_identity
#print axioms arrived_endpoint_increment
#print axioms endpoint_nondecreasing_of_below_geometric_threshold
#print axioms endpoint_decreases_of_above_geometric_threshold
#print axioms endpoint_decreases_iff_geometric_threshold
#print axioms positive_spacing_countermodel
#print axioms left_endpoint_surplus_identity
#print axioms right_endpoint_surplus_identity
#print axioms quadratic_excess_identity

end RHPrimePrefixKickedRecurrence
