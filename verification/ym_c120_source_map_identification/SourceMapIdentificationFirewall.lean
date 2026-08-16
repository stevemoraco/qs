import Mathlib

/-!
# Yang--Mills source-map identification firewall

Finite arithmetic/function algebra only.

The motivating source-audit issue is the following.  A genuine bounded-product
theorem for one normalized Part-V source transport does not automatically bound
a different Section-8 triangular transport merely because both act on the same
finite source multiplet and are measured with the same gauge.  An exact map
identity, a uniformly bounded conjugacy/intertwiner, or a direct Section-8
product estimate is still required.

The countermodel below uses the same carrier, the same initial state, the same
size gauge, and a contractive geometric-averaging map.  The Part-V transport is
the identity and has uniformly bounded products.  The Section-8 transport is
the unit shear `(x,y) ↦ (x+y,y)`; every individual step has a fixed factor-two
bound, but its products on `(0,1)` have size `n+1`.

This file does **not** formalize Kirk's manuscript, Banach source norms,
renormalization, lattice gauge theory, Osterwalder--Schrader reconstruction,
Yang--Mills, or any Clay theorem.
-/

namespace Millennium.YangMills.SourceMapIdentificationFirewall

/-- A common finite source carrier. -/
abbrev SourceState := ℕ × ℕ

/-- One fixed nonnegative size gauge used for both transports. -/
def gauge (v : SourceState) : ℕ := v.1 + v.2

/-- A model Part-V normalized source transport with a genuine bounded product. -/
def partVStep (v : SourceState) : SourceState := v

/-- A model Section-8 unit-upper-triangular source transport. -/
def section8Step (v : SourceState) : SourceState := (v.1 + v.2, v.2)

/-- The geometric averaging part can be perfectly contractive; here it is the
identity, so it cannot be blamed for the product growth. -/
def geometricAverage (v : SourceState) : SourceState := v

/-- Iterate a source step from one common root state. -/
def orbit (step : SourceState → SourceState) : ℕ → SourceState
  | 0 => (0, 1)
  | n + 1 => step (orbit step n)

@[simp] theorem partV_orbit_formula (n : ℕ) :
    orbit partVStep n = (0, 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [orbit, partVStep, ih]

@[simp] theorem section8_orbit_formula (n : ℕ) :
    orbit section8Step n = (n, 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [orbit, section8Step, ih, Nat.succ_eq_add_one, Nat.add_assoc]

/-- The Part-V products are uniformly bounded in the common gauge. -/
theorem partV_products_uniformly_bounded (n : ℕ) :
    gauge (orbit partVStep n) = 1 := by
  simp [gauge]

/-- The geometric averaging map is contractive in the common gauge. -/
theorem geometric_averaging_is_contracting (v : SourceState) :
    gauge (geometricAverage v) ≤ gauge v := by
  simp [geometricAverage]

/-- Every individual Section-8 shear has one fixed factor-two bound. -/
theorem section8_one_step_has_fixed_bound (v : SourceState) :
    gauge (section8Step v) ≤ 2 * gauge v := by
  rcases v with ⟨x, y⟩
  simp [gauge, section8Step]
  omega

/-- Nevertheless the Section-8 product grows exactly linearly with depth. -/
theorem section8_product_exact_growth (n : ℕ) :
    gauge (orbit section8Step n) = n + 1 := by
  simp [gauge]

/-- Hence every proposed depth-independent bound is eventually violated. -/
theorem section8_products_exceed_every_bound (C : ℕ) :
    ∃ n : ℕ, C < gauge (orbit section8Step n) := by
  refine ⟨C, ?_⟩
  rw [section8_product_exact_growth]
  omega

/-- There is no uniform Section-8 product bound in this countermodel. -/
theorem no_uniform_section8_product_bound :
    ¬ ∃ C : ℕ, ∀ n : ℕ, gauge (orbit section8Step n) ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := section8_products_exceed_every_bound C
  exact (not_lt_of_ge (hC n)) hn

/-- Complete no-free-lunch package: same finite carrier and gauge, a genuine
bounded Part-V product theorem, contractive averaging, and fixed one-step
Section-8 bounds can coexist with unbounded Section-8 products. -/
theorem same_carrier_norm_and_partV_product_theorem_do_not_bound_section8 :
    (∀ n : ℕ, gauge (orbit partVStep n) ≤ 1) ∧
    (∀ v : SourceState, gauge (geometricAverage v) ≤ gauge v) ∧
    (∀ v : SourceState, gauge (section8Step v) ≤ 2 * gauge v) ∧
    (∀ C : ℕ, ∃ n : ℕ, C < gauge (orbit section8Step n)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact le_of_eq (partV_products_uniformly_bounded n)
  · exact geometric_averaging_is_contracting
  · exact section8_one_step_has_fixed_bound
  · exact section8_products_exceed_every_bound

/-- A running-depth factor such as a positive power of a running logarithm is
not, by itself, a depth-independent constant.  This is the exponent-one finite
shadow. -/
theorem running_depth_factor_is_not_uniform (C : ℕ) :
    ∃ j : ℕ, C < 1 + j := by
  exact ⟨C, by omega⟩

/-- Exact orbit identification is one sufficient repair: any uniform Part-V
bound then transfers immediately. -/
theorem exact_orbit_identification_transfers_uniform_bound
    {X : Type*}
    (size : X → ℕ)
    (partV section8 : ℕ → X)
    (C : ℕ)
    (hIdent : ∀ n : ℕ, section8 n = partV n)
    (hPartV : ∀ n : ℕ, size (partV n) ≤ C) :
    ∀ n : ℕ, size (section8 n) ≤ C := by
  intro n
  rw [hIdent n]
  exact hPartV n

#print axioms partV_orbit_formula
#print axioms section8_orbit_formula
#print axioms partV_products_uniformly_bounded
#print axioms geometric_averaging_is_contracting
#print axioms section8_one_step_has_fixed_bound
#print axioms section8_product_exact_growth
#print axioms section8_products_exceed_every_bound
#print axioms no_uniform_section8_product_bound
#print axioms same_carrier_norm_and_partV_product_theorem_do_not_bound_section8
#print axioms running_depth_factor_is_not_uniform
#print axioms exact_orbit_identification_transfers_uniform_bound

end Millennium.YangMills.SourceMapIdentificationFirewall
