import Mathlib

namespace NSYuFarFieldYoungTightnessFirewalls

/-!
Finite firewalls for the downstream gates in Yu's filtered-vortex-stretching
architecture.  These statements intentionally make no PDE-realizability claim.

1. Tracelessness of an affine strain jet does not force its stretching quadratic
   form to vanish or be nonpositive.
2. Every fixed finite coordinate window can miss unit mass that escapes to a
   newly activated coordinate.  This is only a finite logical model of the gap
   between cylindrical projection control and full norm tightness.
-/

/-- A concrete symmetric trace-free diagonal strain can still stretch a vector
strictly positively.  Hence incompressibility/tracelessness alone cannot cancel
an affine far-field jet in a stretching estimate. -/
theorem tracefree_diagonal_affine_jet_can_stretch :
    (1 : ℝ) + (-1) + 0 = 0 ∧
      0 < (1 : ℝ) * 1^2 + (-1 : ℝ) * 0^2 + (0 : ℝ) * 0^2 := by
  norm_num

/-- Existential form of the same firewall, written as a diagonal quadratic form. -/
theorem tracefree_does_not_force_zero_stretch :
    ∃ a11 a22 a33 w1 w2 w3 : ℝ,
      a11 + a22 + a33 = 0 ∧
      0 < a11 * w1^2 + a22 * w2^2 + a33 * w3^2 := by
  refine ⟨1, -1, 0, 1, 0, 0, ?_, ?_⟩ <;> norm_num

/-- A finite coordinate escape model: all mass sits at the newly activated
coordinate `N`. -/
def escapingCoordinate (N k : ℕ) : ℝ :=
  if k = N then 1 else 0

@[simp] theorem escapingCoordinate_at_edge (N : ℕ) :
    escapingCoordinate N N = 1 := by
  simp [escapingCoordinate]

/-- Every coordinate strictly below the active edge sees zero. -/
theorem escapingCoordinate_invisible_below
    {N k : ℕ} (hk : k < N) :
    escapingCoordinate N k = 0 := by
  have hne : k ≠ N := Nat.ne_of_lt hk
  simp [escapingCoordinate, hne]

/-- For every prescribed finite observation window, there is a unit edge mass
that is invisible on the whole window.  This is the exact finite no-free-lunch
model behind the need for an additional tightness/full-representation theorem. -/
theorem every_fixed_projection_window_misses_some_unit_escape (K : ℕ) :
    ∃ N : ℕ,
      K < N ∧
      (∀ k : ℕ, k ≤ K → escapingCoordinate N k = 0) ∧
      escapingCoordinate N N = 1 := by
  refine ⟨K + 1, Nat.lt_succ_self K, ?_, escapingCoordinate_at_edge (K + 1)⟩
  intro k hk
  exact escapingCoordinate_invisible_below
    (lt_of_le_of_lt hk (Nat.lt_succ_self K))

/-- The escaping coordinate carries a fixed unit quadratic mass even though all
coordinates in the prescribed lower window vanish. -/
theorem every_fixed_projection_window_misses_unit_quadratic_mass (K : ℕ) :
    ∃ N : ℕ,
      K < N ∧
      (∀ k : ℕ, k ≤ K → escapingCoordinate N k = 0) ∧
      (escapingCoordinate N N)^2 = 1 := by
  rcases every_fixed_projection_window_misses_some_unit_escape K with
    ⟨N, hKN, hlow, hedge⟩
  refine ⟨N, hKN, hlow, ?_⟩
  rw [hedge]
  norm_num

#print axioms tracefree_diagonal_affine_jet_can_stretch
#print axioms tracefree_does_not_force_zero_stretch
#print axioms escapingCoordinate_invisible_below
#print axioms every_fixed_projection_window_misses_some_unit_escape
#print axioms every_fixed_projection_window_misses_unit_quadratic_mass

end NSYuFarFieldYoungTightnessFirewalls
