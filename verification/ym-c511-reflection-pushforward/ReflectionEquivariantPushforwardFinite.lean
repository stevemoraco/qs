import Mathlib

/-!
# Finite reflection-equivariant pushforward theorem

This file formalizes the finite algebraic core of the exact statement that an
exact coarse-graining which intertwines reflections preserves the
Osterwalder--Schrader quadratic form by pullback.

It does not formalize lattice gauge theory, Wilson measures, constructive RG,
continuum OS reconstruction, O(4), nontriviality, or a Yang--Mills mass gap.
-/

open scoped BigOperators

namespace Millennium.YangMills.ReflectionEquivariantPushforwardFinite

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Exact weight of a finite pushforward fibre. -/
def pushWeight [DecidableEq Y] (mu : X → ℝ) (B : X → Y) (y : Y) : ℝ :=
  ∑ x : {x : X // B x = y}, mu x

/-- Real finite Osterwalder--Schrader pairing. -/
def osPair (mu : X → ℝ) (theta : X → X) (f g : X → ℝ) : ℝ :=
  ∑ x : X, mu x * f (theta x) * g x

/-- Before using reflection equivariance, a pushforward OS pairing is exactly
one fine-space fibrewise sum. -/
theorem pushforward_pair_identity [DecidableEq Y]
    (mu : X → ℝ) (B : X → Y) (thetaY : Y → Y) (f g : Y → ℝ) :
    osPair (pushWeight mu B) thetaY f g =
      ∑ x : X, mu x * f (thetaY (B x)) * g (B x) := by
  classical
  unfold osPair pushWeight
  calc
    (∑ y : Y, (∑ x : {x : X // B x = y}, mu x) * f (thetaY y) * g y) =
        ∑ y : Y, ∑ x : {x : X // B x = y},
          mu x * f (thetaY y) * g y := by
      apply Finset.sum_congr rfl
      intro y hy
      simp [Finset.sum_mul]
    _ = ∑ y : Y, ∑ x : {x : X // B x = y},
          mu x * f (thetaY (B x)) * g (B x) := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro x hx
      simp [x.property]
    _ = ∑ x : X, mu x * f (thetaY (B x)) * g (B x) := by
      simpa using
        (Fintype.sum_fiberwise B
          (fun x : X => mu x * f (thetaY (B x)) * g (B x)))

/-- Exact reflection equivariance turns the pushforward pairing into the fine
pairing of pullback observables. -/
theorem equivariant_pushforward_pair [DecidableEq Y]
    (mu : X → ℝ) (B : X → Y) (thetaX : X → X) (thetaY : Y → Y)
    (hB : ∀ x, B (thetaX x) = thetaY (B x)) (f g : Y → ℝ) :
    osPair (pushWeight mu B) thetaY f g =
      osPair mu thetaX (f ∘ B) (g ∘ B) := by
  rw [pushforward_pair_identity]
  unfold osPair
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Function.comp_apply]
  rw [hB x]

/-- Reflection positivity on a selected finite observable class. -/
def ReflectionPositiveOn
    (mu : X → ℝ) (theta : X → X) (A : Set (X → ℝ)) : Prop :=
  ∀ f, f ∈ A → 0 ≤ osPair mu theta f f

/-- Every exact reflection-equivariant finite pushforward preserves reflection
positivity on every coarse class whose pullbacks lie in the fine positive-time
class. -/
theorem reflectionPositive_pushforward [DecidableEq Y]
    (mu : X → ℝ) (B : X → Y) (thetaX : X → X) (thetaY : Y → Y)
    (hB : ∀ x, B (thetaX x) = thetaY (B x))
    (AX : Set (X → ℝ)) (AY : Set (Y → ℝ))
    (hmu : ReflectionPositiveOn mu thetaX AX)
    (hpull : ∀ f, f ∈ AY → (f ∘ B) ∈ AX) :
    ReflectionPositiveOn (pushWeight mu B) thetaY AY := by
  intro f hf
  rw [equivariant_pushforward_pair mu B thetaX thetaY hB f f]
  exact hmu (f ∘ B) (hpull f hf)

/-- The reflection form of the positive-probability perturbation

`[[1/4-e,1/4+e],[1/4+e,1/4-e]]`

on the vector `(x,y)`. -/
noncomputable def perturbedBitForm (e x y : ℝ) : ℝ :=
  (1 / 4 - e) * x * x + (1 / 4 + e) * x * y +
    (1 / 4 + e) * y * x + (1 / 4 - e) * y * y

/-- The antisymmetric OS direction becomes strictly negative under every
positive off-diagonal perturbation. -/
theorem perturbedBitForm_antisymmetric_negative
    (e : ℝ) (he : 0 < e) :
    perturbedBitForm e 1 (-1) < 0 := by
  have hid : perturbedBitForm e 1 (-1) = -4 * e := by
    unfold perturbedBitForm
    ring
  rw [hid]
  linarith

/-- Arbitrarily small positive probability perturbations can destroy
reflection positivity when the exact form has a null direction. -/
theorem positive_probability_perturbation_breaks_reflection_positivity
    (e : ℝ) (he : 0 < e) (heq : e < 1 / 4) :
    0 < 1 / 4 - e ∧
    0 < 1 / 4 + e ∧
    2 * (1 / 4 - e) + 2 * (1 / 4 + e) = 1 ∧
    perturbedBitForm e 1 (-1) < 0 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · ring
  · exact perturbedBitForm_antisymmetric_negative e he

#print axioms pushforward_pair_identity
#print axioms equivariant_pushforward_pair
#print axioms reflectionPositive_pushforward
#print axioms perturbedBitForm_antisymmetric_negative
#print axioms positive_probability_perturbation_breaks_reflection_positivity

end Millennium.YangMills.ReflectionEquivariantPushforwardFinite
