import Mathlib

/-!
# High-vorticity component chain firewall

Finite algebra only.  These statements formalize the quantitative endgame used
when a fixed-filter spatial cover turns a same-time high-vorticity component
into a bounded-hop chain.

The source-native motivation is Yu's pairwise defect (arXiv:2606.27560,
Eq. (2.15)), whose angular factor is linear in
`|xi(x)-xi(x-z)|`, not quadratic.  Accordingly the defect floor below is
linear in the extracted local angular jump.

They do NOT prove that a Navier--Stokes vorticity superlevel set is connected,
that a Euclidean cover gives the required chain, or that one pointwise local
jump produces a uniform positive-measure contribution to Yu's integrated
defect.  Those remain PDE/geometry bridges.
-/

namespace NSHighVorticityComponentChain

/-- Once a geometric argument gives a route of at most `cover` effective hops,
a total directional separation `gap` forces one local jump of size at least
`gap / cover`. -/
theorem bounded_cover_forces_local_jump
    {gap cover localJump : ℝ}
    (hcover : 0 < cover)
    (hroute : gap ≤ cover * localJump) :
    gap / cover ≤ localJump := by
  apply (div_le_iff₀ hcover).2
  simpa [mul_comm] using hroute

/-- A lower bound for one local angular jump becomes a lower bound for any
nonnegative weighted *linear* defect that dominates that jump.  This matches
the angular power in Yu's pairwise defect. -/
theorem local_jump_forces_weighted_linear_defect
    {weight gap cover localJump defect : ℝ}
    (hweight : 0 ≤ weight)
    (hlocal : gap / cover ≤ localJump)
    (hdefect : weight * localJump ≤ defect) :
    weight * (gap / cover) ≤ defect := by
  exact le_trans (mul_le_mul_of_nonneg_left hlocal hweight) hdefect

/-- At a fixed finite cover size, positive magnitude weight and positive global
separation produce a strictly positive source-native linear defect floor. -/
theorem fixed_cover_positive_linear_defect_floor
    {weight gap cover : ℝ}
    (hweight : 0 < weight)
    (hgap : 0 < gap)
    (hcover : 0 < cover) :
    0 < weight * (gap / cover) := by
  positivity

/-- If the number of effective hops is allowed to grow, a fixed total turn can
be distributed evenly with local jump `gap / cover`.  For a *linear* angular
currency the total of all equal hops is nevertheless exactly the original gap;
this is why summing local Yu-type contributions is potentially stronger than
keeping only the largest single hop. -/
theorem exact_diffuse_turn
    {gap cover : ℝ}
    (hcover : cover ≠ 0) :
    cover * (gap / cover) = gap := by
  field_simp [hcover]

/-- An explicit finite family: `m+1` equal hops each of size `1/(m+1)` carry a
unit total turn while the individual hop size decreases with the number of
hops. -/
theorem diffuse_turn_family (m : ℕ) :
    0 < (1 : ℝ) / (m + 1) ∧
      ((m + 1 : ℝ) * ((1 : ℝ) / (m + 1)) = 1) := by
  have hpos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  constructor
  · positivity
  · field_simp

#print axioms bounded_cover_forces_local_jump
#print axioms local_jump_forces_weighted_linear_defect
#print axioms fixed_cover_positive_linear_defect_floor
#print axioms exact_diffuse_turn
#print axioms diffuse_turn_family

end NSHighVorticityComponentChain
