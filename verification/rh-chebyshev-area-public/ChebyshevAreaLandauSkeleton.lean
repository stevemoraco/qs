import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Lean proof skeleton for Johnston's Chebyshev-area RH criterion

This file formalizes the exact logical shape of the published analytic argument.
It deliberately does **not** postulate the missing prime-area sign as an axiom.
Instead, every remaining analytic input is a named field of `LandauBridge`:

* an abscissa bounded above by `2`;
* Landau's real-singularity theorem under eventual nonnegativity;
* regularity on the real interval `(3/2, 2]`;
* the fact that every nontrivial zero with real part above `1/2` pushes the
  abscissa at least to `1 + re rho`.

Unlike the first skeleton, reflection of nontrivial zeros is proved directly
from Mathlib's completed-zeta functional equation, Gamma-factor zero
classification, and zeta nonvanishing for `re s ≥ 1`.

The file is a quantifier and dependency firewall. It is not a proof of any
analytic field of `LandauBridge`, and it is not a proof of positivity of the
genuine integrated Chebyshev deficit.
-/

namespace Millennium.RH.ChebyshevAreaLandau

open Complex

/-- Mathlib's nontrivial-zero conditions, packaged for reuse. -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
    (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧
    s ≠ 1

/-- Eventual nonnegativity of a real-valued area. -/
def EventuallyNonnegative (A : ℝ → ℝ) : Prop :=
  ∃ X : ℝ, ∀ x : ℝ, X ≤ x → 0 ≤ A x

/-- Johnston's strict sign condition, abstracted from the genuine area. -/
def PositiveAfterTwo (A : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 2 < x → 0 < A x

/-- No nontrivial zeta zero lies strictly to the right of the critical line. -/
def RightHalfBound : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → s.re ≤ (1 : ℝ) / 2

/-- No nontrivial zeta zero lies strictly to the left of the critical line. -/
def LeftHalfBound : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → (1 : ℝ) / 2 ≤ s.re

/-- A packaged nontrivial zero cannot be zero. -/
lemma nontrivialZero_ne_zero {s : ℂ} (hs : IsNontrivialZero s) : s ≠ 0 := by
  intro h
  subst s
  have hz := hs.1
  rw [riemannZeta_zero] at hz
  norm_num at hz

/-- The real Gamma factor is nonzero at every packaged nontrivial zero. -/
lemma GammaR_ne_zero_of_nontrivialZero
    {s : ℂ} (hs : IsNontrivialZero s) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
  intro n hn
  cases n with
  | zero =>
      simp only [Nat.cast_zero, mul_zero, neg_zero] at hn
      exact nontrivialZero_ne_zero hs hn
  | succ n =>
      apply hs.2.1
      refine ⟨n, ?_⟩
      simpa [Nat.cast_add, Nat.cast_one] using hn

/-- A nontrivial zeta zero is a zero of the completed zeta function. -/
lemma completedRiemannZeta_eq_zero_of_nontrivialZero
    {s : ℂ} (hs : IsNontrivialZero s) :
    completedRiemannZeta s = 0 := by
  have hs0 : s ≠ 0 := nontrivialZero_ne_zero hs
  have hGamma : Gammaℝ s ≠ 0 := GammaR_ne_zero_of_nontrivialZero hs
  have hz := hs.1
  rw [riemannZeta_def_of_ne_zero hs0] at hz
  exact (div_eq_zero_iff.mp hz).resolve_right hGamma

/-- The functional equation gives a reflected zeta zero. -/
lemma reflected_riemannZeta_zero
    {s : ℂ} (hs : IsNontrivialZero s) :
    riemannZeta (1 - s) = 0 := by
  have hs1 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs.2.2)
  rw [riemannZeta_def_of_ne_zero hs1, completedRiemannZeta_one_sub,
    completedRiemannZeta_eq_zero_of_nontrivialZero hs, zero_div]

/-- A reflected nontrivial zero is not a negative even integer. -/
lemma reflected_not_trivial
    {s : ℂ} (hs : IsNontrivialZero s) :
    ¬ ∃ n : ℕ, 1 - s = -2 * (n + 1) := by
  rintro ⟨n, hn⟩
  have hsform : s = 1 + 2 * (n + 1) := by
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 - (-2 * (n + 1)) := by rw [hn]
      _ = 1 + 2 * (n + 1) := by ring
  have hre : 1 ≤ s.re := by
    rw [hsform]
    norm_num
    positivity
  exact (riemannZeta_ne_zero_of_one_le_re hre) hs.1

/-- A reflected nontrivial zero is not the pole at one. -/
lemma reflected_ne_one
    {s : ℂ} (hs : IsNontrivialZero s) :
    1 - s ≠ 1 := by
  intro h
  apply nontrivialZero_ne_zero hs
  calc
    s = 1 - (1 - s) := by ring
    _ = 1 - 1 := by rw [h]
    _ = 0 := by ring

/-- Every packaged nontrivial zero reflects to another packaged nontrivial zero. -/
theorem reflectsNontrivialZeros :
    ∀ s : ℂ, IsNontrivialZero s → IsNontrivialZero (1 - s) := by
  intro s hs
  exact ⟨reflected_riemannZeta_zero hs, reflected_not_trivial hs,
    reflected_ne_one hs⟩

/-- Upper and lower critical-line bounds imply Mathlib's actual RH statement. -/
theorem riemannHypothesis_of_bounds
    (hupper : RightHalfBound)
    (hlower : LeftHalfBound) :
    RiemannHypothesis := by
  intro s hz htrivial h_one
  have hs : IsNontrivialZero s := ⟨hz, htrivial, h_one⟩
  exact le_antisymm (hupper s hs) (hlower s hs)

/-- Reflection converts a right-half bound into the corresponding left-half bound. -/
theorem leftHalfBound_of_reflection
    (hupper : RightHalfBound) :
    LeftHalfBound := by
  intro s hs
  have h := hupper (1 - s) (reflectsNontrivialZeros s hs)
  simp only [sub_re, one_re] at h
  linarith

/--
The exact analytic interfaces used by the Landau/Mellin converse.

`singular σ` means that the analytically continued Mellin transform is singular
at the real point `σ`. Keeping it abstract prevents the Lean theorem from
silently claiming that meromorphic continuation, prime-zeta Möbius inversion,
or Landau's theorem have already been formalized.
-/
structure LandauBridge (A : ℝ → ℝ) where
  /-- Predicate saying that the continued Mellin transform is singular at a real point. -/
  singular : ℝ → Prop
  /-- Abscissa of convergence of the nonnegative tail Mellin transform. -/
  abscissa : ℝ
  /-- Elementary growth gives convergence to the right of `2`. -/
  abscissa_le_two : abscissa ≤ 2
  /-- Landau: an eventually nonnegative tail is singular at its real abscissa. -/
  landau_real_singularity : EventuallyNonnegative A → singular abscissa
  /-- The explicit prime-zeta continuation is regular at every real point in `(3/2,2]`. -/
  real_regular :
    ∀ σ : ℝ, (3 : ℝ) / 2 < σ → σ ≤ 2 → ¬ singular σ
  /-- An off-line zero at `s` forces the Mellin abscissa at least to `1 + re s`. -/
  offLineZero_pushes_abscissa :
    ∀ s : ℂ, IsNontrivialZero s →
      (1 : ℝ) / 2 < s.re → 1 + s.re ≤ abscissa

/-- Eventual area nonnegativity plus the Landau bridge excludes every right-half zero. -/
theorem rightHalfBound_of_eventualNonnegative
    {A : ℝ → ℝ}
    (bridge : LandauBridge A)
    (hA : EventuallyNonnegative A) :
    RightHalfBound := by
  intro s hs
  by_contra hnot
  have hright : (1 : ℝ) / 2 < s.re := lt_of_not_ge hnot
  have habscissa_lower : 1 + s.re ≤ bridge.abscissa :=
    bridge.offLineZero_pushes_abscissa s hs hright
  have habscissa_gt : (3 : ℝ) / 2 < bridge.abscissa := by
    linarith
  exact
    (bridge.real_regular bridge.abscissa habscissa_gt bridge.abscissa_le_two)
      (bridge.landau_real_singularity hA)

/-- The complete conditional converse from eventual area nonnegativity to RH. -/
theorem riemannHypothesis_of_eventualNonnegative
    {A : ℝ → ℝ}
    (bridge : LandauBridge A)
    (hA : EventuallyNonnegative A) :
    RiemannHypothesis := by
  have hupper : RightHalfBound :=
    rightHalfBound_of_eventualNonnegative bridge hA
  have hlower : LeftHalfBound :=
    leftHalfBound_of_reflection hupper
  exact riemannHypothesis_of_bounds hupper hlower

/-- Johnston's strict sign condition implies eventual nonnegativity. -/
theorem eventuallyNonnegative_of_positiveAfterTwo
    {A : ℝ → ℝ}
    (hA : PositiveAfterTwo A) :
    EventuallyNonnegative A := by
  refine ⟨3, ?_⟩
  intro x hx
  exact (hA x (by linarith)).le

/-- Johnston's strict sign condition plus the Landau bridge implies RH. -/
theorem riemannHypothesis_of_positiveAfterTwo
    {A : ℝ → ℝ}
    (bridge : LandauBridge A)
    (hA : PositiveAfterTwo A) :
    RiemannHypothesis :=
  riemannHypothesis_of_eventualNonnegative bridge
    (eventuallyNonnegative_of_positiveAfterTwo hA)

/-- Once the RH-to-area direction is supplied, eventual nonnegativity is equivalent to RH. -/
theorem riemannHypothesis_iff_eventuallyNonnegative
    {A : ℝ → ℝ}
    (bridge : LandauBridge A)
    (rh_implies_area : RiemannHypothesis → EventuallyNonnegative A) :
    RiemannHypothesis ↔ EventuallyNonnegative A := by
  constructor
  · exact rh_implies_area
  · exact riemannHypothesis_of_eventualNonnegative bridge

/-- Exact abstract Johnston endpoint: RH iff the strict area sign, once its analytic directions are supplied. -/
theorem riemannHypothesis_iff_positiveAfterTwo
    {A : ℝ → ℝ}
    (bridge : LandauBridge A)
    (rh_implies_positive : RiemannHypothesis → PositiveAfterTwo A) :
    RiemannHypothesis ↔ PositiveAfterTwo A := by
  constructor
  · exact rh_implies_positive
  · exact riemannHypothesis_of_positiveAfterTwo bridge

#print axioms nontrivialZero_ne_zero
#print axioms GammaR_ne_zero_of_nontrivialZero
#print axioms completedRiemannZeta_eq_zero_of_nontrivialZero
#print axioms reflected_riemannZeta_zero
#print axioms reflected_not_trivial
#print axioms reflected_ne_one
#print axioms reflectsNontrivialZeros
#print axioms riemannHypothesis_of_bounds
#print axioms leftHalfBound_of_reflection
#print axioms rightHalfBound_of_eventualNonnegative
#print axioms riemannHypothesis_of_eventualNonnegative
#print axioms eventuallyNonnegative_of_positiveAfterTwo
#print axioms riemannHypothesis_of_positiveAfterTwo
#print axioms riemannHypothesis_iff_eventuallyNonnegative
#print axioms riemannHypothesis_iff_positiveAfterTwo

end Millennium.RH.ChebyshevAreaLandau
