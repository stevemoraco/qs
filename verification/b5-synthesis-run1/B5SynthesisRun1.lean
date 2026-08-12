import Mathlib

namespace B5SynthesisRun1.RH

/-- The B4 two-atom closure by first two moments does not extend even to three atoms. -/
theorem three_atom_first_two_moments_not_faithful :
    ((0 : ℤ) + 0 + 3 = (-1) + 2 + 2) ∧
      ((0 : ℤ)^2 + 0^2 + 3^2 = (-1)^2 + 2^2 + 2^2) ∧
      ((0 : ℤ)^3 + 0^3 + 3^3 ≠ (-1)^3 + 2^3 + 2^3) := by
  norm_num

#print axioms three_atom_first_two_moments_not_faithful

end B5SynthesisRun1.RH

namespace B5SynthesisRun1.PNP

open Finset

/-- If every decoder success set has at most `K` inputs, an input-dependent selector
that succeeds everywhere must use enough distinct decoders to cover the whole input set. -/
theorem selector_cover_capacity
    {X D : Type*} [Fintype X] [Fintype D] [DecidableEq X] [DecidableEq D]
    (success : D → Finset X)
    (sel : X → D)
    (hsolve : ∀ x, x ∈ success (sel x))
    (K : ℕ)
    (hcap : ∀ d, #(success d) ≤ K) :
    Fintype.card X ≤ #(Finset.univ.image sel) * K := by
  let R : Finset D := Finset.univ.image sel
  have hsubset : (Finset.univ : Finset X) ⊆ R.biUnion success := by
    intro x hx
    have hd : sel x ∈ R := by
      dsimp [R]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨sel x, hd, hsolve x⟩
  calc
    Fintype.card X = #(Finset.univ : Finset X) := by simp
    _ ≤ #(R.biUnion success) := Finset.card_le_card hsubset
    _ ≤ ∑ d ∈ R, #(success d) := Finset.card_biUnion_le
    _ ≤ ∑ d ∈ R, K := by
      gcongr with d hd
      exact hcap d
    _ = #R * K := by simp
    _ = #(Finset.univ.image sel) * K := by rfl

#print axioms selector_cover_capacity

end B5SynthesisRun1.PNP

namespace B5SynthesisRun1.BSD

/-- Truncated length of one Smith summand at finite level `k`; this is `min a k`. -/
def truncLength (a k : ℕ) : ℕ := if a < k then a else k

/-- A single Smith summand contributes no new finite-level length between `p-1`
and `p` exactly when its depth is already below `p`. -/
theorem smith_summand_stabilizes_iff_depth_below
    (a p : ℕ) (hp : 0 < p) :
    truncLength a p = truncLength a (p - 1) ↔ a < p := by
  constructor
  · intro hstab
    by_contra hnot
    have hnotp : ¬ a < p := by omega
    have hnotp1 : ¬ a < p - 1 := by omega
    simp [truncLength, hnotp, hnotp1] at hstab
    omega
  · intro h
    by_cases h2 : a < p - 1
    · simp [truncLength, h, h2]
    · have heq : a = p - 1 := by omega
      have hprev : p - 1 < p := by omega
      simp [truncLength, heq, hprev]

#print axioms smith_summand_stabilizes_iff_depth_below

end B5SynthesisRun1.BSD

namespace B5SynthesisRun1.Hodge

/-- If the target carrier is cyclic and the desired property is stable under the
carrier action, one proved generator transfers the property to the whole carrier. -/
theorem cyclic_stable_property_closes
    {K W : Type*} [SMul K W]
    (Alg : W → Prop) (w : W)
    (hcyclic : ∀ x : W, ∃ k : K, x = k • w)
    (hstable : ∀ (k : K) {x : W}, Alg x → Alg (k • x))
    (hw : Alg w) :
    ∀ x : W, Alg x := by
  intro x
  rcases hcyclic x with ⟨k, hk⟩
  rw [hk]
  exact hstable k hw

#print axioms cyclic_stable_property_closes

end B5SynthesisRun1.Hodge

namespace B5SynthesisRun1.NavierStokes

/-- Scalar parabolic-bubble arithmetic: with amplitude `b^3` and spacetime volume
`b^-15`, the critical fifth-power cost is exactly one while the energy-class
`10/3` proxy is `b^-5`. -/
theorem critical_cost_fixed_energy_proxy_decays
    (b : ℝ) (hb : b ≠ 0) :
    (b^3)^5 * (1 / b^15) = 1 ∧
      b^10 * (1 / b^15) = 1 / b^5 := by
  constructor
  · field_simp [hb]
  · field_simp [hb]

#print axioms critical_cost_fixed_energy_proxy_decays

end B5SynthesisRun1.NavierStokes

namespace B5SynthesisRun1.YangMills

/-- A regulator-dependent physical mass estimate with error below half the target
has a uniform positive half-gap. This is the pointwise core of the `o(a)` margin. -/
theorem half_gap_from_small_ratio_error
    (a M eps g : ℝ)
    (ha : 0 < a) (hM : 0 < M)
    (hsmall : eps < M / 2)
    (herr : |g / a - M| ≤ eps) :
    M / 2 < g / a := by
  have hlow := (abs_le.mp herr).1
  linarith

#print axioms half_gap_from_small_ratio_error

end B5SynthesisRun1.YangMills
