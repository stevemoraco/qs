namespace YMFlagGaugeOrbitFirewall

/-!
# Finite logical core of the Yang–Mills flag/gauge-orbit firewall

A regular conjugacy orbit is a transitive `G`-space (geometrically `G/T`).
Any scalar observable invariant under that action is constant on the orbit.
Therefore a nonconstant/positive-variance flag observable cannot itself be a
pointwise gauge-invariant scalar.

This file is pure Lean and contains no analytic or Yang–Mills axioms.  It does
not prove or disprove the Clay problem; it formalizes the finite orbit logic
that any flag-to-physical-observable transfer must overcome.
-/

universe uG uX uY

/-- Transitivity of an abstract action.  No group laws are needed for the
logical obstruction. -/
def IsTransitive {G : Type uG} {X : Type uX}
    (act : G → X → X) : Prop :=
  ∀ x y : X, ∃ g : G, act g x = y

/-- Invariance of a scalar/vector-valued observable under the action. -/
def IsInvariant {G : Type uG} {X : Type uX} {Y : Type uY}
    (act : G → X → X) (f : X → Y) : Prop :=
  ∀ g : G, ∀ x : X, f (act g x) = f x

/-- An invariant observable on a transitive orbit is constant. -/
theorem invariant_on_transitive_orbit_constant
    {G : Type uG} {X : Type uX} {Y : Type uY}
    (act : G → X → X) (f : X → Y)
    (htrans : IsTransitive act)
    (hinv : IsInvariant act f) :
    ∀ x y : X, f x = f y := by
  intro x y
  obtain ⟨g, hg⟩ := htrans x y
  rw [← hg]
  exact (hinv g x).symm

/-- Contrapositive form: a nonconstant flag observable is not invariant. -/
theorem nonconstant_flag_not_invariant
    {G : Type uG} {X : Type uX} {Y : Type uY}
    (act : G → X → X) (f : X → Y)
    (htrans : IsTransitive act)
    (hnonconstant : ∃ x y : X, f x ≠ f y) :
    ¬ IsInvariant act f := by
  intro hinv
  obtain ⟨x, y, hxy⟩ := hnonconstant
  exact hxy (invariant_on_transitive_orbit_constant act f htrans hinv x y)

/-- Constructive witness form: if a flag observable distinguishes two points,
then some gauge-orbit move changes its value. -/
theorem nonconstant_flag_has_gauge_variation
    {G : Type uG} {X : Type uX} {Y : Type uY}
    (act : G → X → X) (f : X → Y)
    (htrans : IsTransitive act)
    (hnonconstant : ∃ x y : X, f x ≠ f y) :
    ∃ g : G, ∃ x : X, f (act g x) ≠ f x := by
  obtain ⟨x, y, hxy⟩ := hnonconstant
  obtain ⟨g, hg⟩ := htrans x y
  refine ⟨g, x, ?_⟩
  rw [hg]
  exact hxy.symm

/-- No observable can simultaneously be invariant and distinguish two points
of a transitive orbit. -/
theorem invariant_and_positive_flag_signal_incompatible
    {G : Type uG} {X : Type uX} {Y : Type uY}
    (act : G → X → X) (f : X → Y)
    (htrans : IsTransitive act) :
    IsInvariant act f → (∃ x y : X, f x ≠ f y) → False := by
  intro hinv hsignal
  exact nonconstant_flag_not_invariant act f htrans hsignal hinv

#print axioms invariant_on_transitive_orbit_constant
#print axioms nonconstant_flag_not_invariant
#print axioms nonconstant_flag_has_gauge_variation
#print axioms invariant_and_positive_flag_signal_incompatible

end YMFlagGaugeOrbitFirewall
