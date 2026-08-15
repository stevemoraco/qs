import Mathlib

/-!
# Navier--Stokes direction-concurrency firewall

Finite companion to the Yu / Lei--Ren--Tian interface audit.

Yu's pairwise direction defect compares spatially separated filtered-vorticity
directions at the same time.  Aggregate spacetime mass in two separated
direction sectors therefore does not force a positive pair-defect floor unless
the sector masses overlap in time.

This file formalizes only the finite two-time algebra of that quantifier issue.
It does not formalize vorticity, time slices, measures, Yu's PDE estimate,
Lei--Ren--Tian's direction set, or any Navier--Stokes/Clay conclusion.
-/

namespace NSDirectionConcurrencyFirewall

/-- Aggregate mass of one direction sector over two time slices. -/
def aggregateMass (a₀ a₁ : ℝ) : ℝ := a₀ + a₁

/-- Same-time overlap currency of two direction sectors over two time slices. -/
def overlapMass (a₀ a₁ b₀ b₁ : ℝ) : ℝ := a₀ * b₀ + a₁ * b₁

/-- Ordered same-time pair-defect contribution when the directional separation
cost is `d`. -/
def twoTimeDefect (a₀ a₁ b₀ b₁ d : ℝ) : ℝ :=
  2 * d * overlapMass a₀ a₁ b₀ b₁

theorem defect_eq_two_d_overlap (a₀ a₁ b₀ b₁ d : ℝ) :
    twoTimeDefect a₀ a₁ b₀ b₁ d =
      2 * d * overlapMass a₀ a₁ b₀ b₁ := by
  rfl

/-- Two sectors can each have total mass one while occurring on disjoint time
slices, leaving the same-time pair defect exactly zero. -/
theorem asynchronous_mass_without_concurrent_defect :
    aggregateMass 1 0 = 1 ∧
    aggregateMass 0 1 = 1 ∧
    overlapMass 1 0 0 1 = 0 ∧
    twoTimeDefect 1 0 0 1 1 = 0 := by
  norm_num [aggregateMass, overlapMass, twoTimeDefect]

/-- A lower bound on the time-overlap currency transfers directly to the pair
defect once the directional separation cost is nonnegative. -/
theorem overlap_lower_bound_transfers_to_defect
    {a₀ a₁ b₀ b₁ d q : ℝ}
    (hd : 0 ≤ d)
    (hover : q ≤ overlapMass a₀ a₁ b₀ b₁) :
    2 * d * q ≤ twoTimeDefect a₀ a₁ b₀ b₁ d := by
  unfold twoTimeDefect
  exact mul_le_mul_of_nonneg_left hover (by positivity)

/-- Positive overlap and positive directional separation force a strictly
positive same-time defect floor. -/
theorem positive_overlap_forces_positive_defect
    {a₀ a₁ b₀ b₁ d q : ℝ}
    (hd : 0 < d) (hq : 0 < q)
    (hover : q ≤ overlapMass a₀ a₁ b₀ b₁) :
    0 < twoTimeDefect a₀ a₁ b₀ b₁ d := by
  have hlow : 2 * d * q ≤ twoTimeDefect a₀ a₁ b₀ b₁ d :=
    overlap_lower_bound_transfers_to_defect (le_of_lt hd) hover
  have hpos : 0 < 2 * d * q := by positivity
  exact lt_of_lt_of_le hpos hlow

/-- Small same-time defect does not constrain aggregate sector masses in the
asynchronous model: both aggregate masses stay exactly one for every requested
positive error threshold. -/
theorem arbitrary_small_defect_with_full_aggregate_masses
    {eta : ℝ} (heta : 0 < eta) :
    aggregateMass 1 0 = 1 ∧
    aggregateMass 0 1 = 1 ∧
    twoTimeDefect 1 0 0 1 1 < eta := by
  constructor
  · norm_num [aggregateMass]
  constructor
  · norm_num [aggregateMass]
  · norm_num [twoTimeDefect, overlapMass]
    exact heta

#print axioms defect_eq_two_d_overlap
#print axioms asynchronous_mass_without_concurrent_defect
#print axioms overlap_lower_bound_transfers_to_defect
#print axioms positive_overlap_forces_positive_defect
#print axioms arbitrary_small_defect_with_full_aggregate_masses

end NSDirectionConcurrencyFirewall
