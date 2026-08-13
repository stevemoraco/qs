import Mathlib

/-!
# B2 Round 52: scale, promise, parity, nilpotent, and residual firewalls

Finite/logical companions to the current six-lane hostile audit.  These theorems
are deliberately weaker than every official Millennium statement.
-/

namespace B2Round52

/-- A logically disjoint promise always has a total propositional completion.
This is set-theoretic only; it says nothing about circuit size. -/
theorem pnp_disjoint_promise_has_logical_completion
    {α : Type*} (U V : Set α)
    (hUV : ∀ x, x ∈ U → x ∉ V) :
    ∃ f : α → Prop,
      (∀ x, x ∈ U → f x) ∧
      (∀ x, x ∈ V → ¬ f x) := by
  refine ⟨fun x => x ∈ U, ?_, ?_⟩
  · intro x hx
    exact hx
  · intro x hxV hxU
    exact hUV x hxU hxV

/-- Residual smallness alone is not enough if coercivity degenerates at the
same squared scale: the normalized penalty stays exactly one. -/
theorem rh_residual_coercivity_ratio_stays_one
    {r : ℝ} (hr : r ≠ 0) :
    r ^ 2 / r ^ 2 = 1 := by
  exact div_self (pow_ne_zero 2 hr)

/-- The parity implication used by the BSD finite core does not require
nonnegative correction valuations: it survives verbatim over the integers. -/
theorem bsd_signed_even_correction
    {lval h correction a b : ℤ}
    (hlval : lval = 2 * a)
    (hh : h = 2 * b)
    (hcontrol : lval = h + correction) :
    ∃ d : ℤ, correction = 2 * d := by
  refine ⟨a - b, ?_⟩
  omega

/-- A concrete square-zero endomorphism model. -/
def hodgeNilpotent (p : ℚ × ℚ) : ℚ × ℚ := (p.2, 0)

theorem hodge_nilpotent_square_zero (p : ℚ × ℚ) :
    hodgeNilpotent (hodgeNilpotent p) = (0, 0) := by
  rcases p with ⟨x, y⟩
  simp [hodgeNilpotent]

/-- Square-zero does not imply that the endomorphism itself is zero. -/
theorem hodge_nilpotent_nonzero :
    hodgeNilpotent ((0, 1) : ℚ × ℚ) ≠ (0, 0) := by
  norm_num [hodgeNilpotent]

/-- An arbitrarily small additive residual destroys exact finite-scale
absorption: with `theta=1/2`, `eta=0`, and `X=2 eps`, the contaminated
contraction is satisfied while `X` is still strictly positive. -/
theorem ns_additive_residual_counterexample
    (eps : ℝ) (heps : 0 < eps) :
    let X := 2 * eps
    let D := 0
    let theta := (1 : ℝ) / 2
    let eta := 0
    0 ≤ X ∧
      0 ≤ D ∧
      theta + eta < 1 ∧
      X + D ≤ theta * X + eta * X + eps ∧
      X ≠ 0 := by
  dsimp
  constructor
  · nlinarith
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · nlinarith
  · nlinarith

/-- Absolute smallness of both a spectral threshold and a transfer defect does
not imply the relative budget required by the finite tightness theorem. -/
theorem ym_absolute_smallness_not_relative
    (eps : ℝ) (heps : 0 < eps) :
    let delta := eps / 4
    let budget := eps / 2
    0 < delta ∧
      delta < eps ∧
      0 < budget ∧
      budget < eps ∧
      delta / 2 < budget := by
  dsimp
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

#print axioms pnp_disjoint_promise_has_logical_completion
#print axioms rh_residual_coercivity_ratio_stays_one
#print axioms bsd_signed_even_correction
#print axioms hodge_nilpotent_square_zero
#print axioms hodge_nilpotent_nonzero
#print axioms ns_additive_residual_counterexample
#print axioms ym_absolute_smallness_not_relative

end B2Round52
