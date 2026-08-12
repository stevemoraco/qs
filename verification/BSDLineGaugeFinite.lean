import Mathlib

/-!
# Finite algebra for basis-free rank-one BSD line data

Honesty boundary: these theorems verify only scalar/unit identities modelling
coordinate changes in rank-one lines. They do not formalize Selmer complexes,
elliptic units, characteristic ideals, determinant functors, p-adic L-functions,
period maps, or the Birch--Swinnerton-Dyer conjecture.
-/

namespace MillenniumBraid.BSDLineGauge

def AssociatedByUnit {R : Type*} [CommRing R] (x y : R) : Prop :=
  ∃ u : Rˣ, y = (u : R) * x

theorem associatedByUnit_refl {R : Type*} [CommRing R] (x : R) :
    AssociatedByUnit x x := by
  refine ⟨1, ?_⟩
  simp

theorem associatedByUnit_symm {R : Type*} [CommRing R] {x y : R}
    (h : AssociatedByUnit x y) : AssociatedByUnit y x := by
  rcases h with ⟨u, rfl⟩
  refine ⟨u⁻¹, ?_⟩
  simp

theorem associatedByUnit_trans {R : Type*} [CommRing R] {x y z : R}
    (hxy : AssociatedByUnit x y) (hyz : AssociatedByUnit y z) :
    AssociatedByUnit x z := by
  rcases hxy with ⟨u, rfl⟩
  rcases hyz with ⟨v, rfl⟩
  refine ⟨v * u, ?_⟩
  simpa [mul_assoc]

theorem unit_rescaling_associated {R : Type*} [CommRing R]
    (u : Rˣ) (x : R) : AssociatedByUnit x ((u : R) * x) := by
  exact ⟨u, rfl⟩

theorem gaugeProductInvariant {R : Type*} [CommRing R]
    (a : Rˣ) (L δ : R) :
    ((↑(a⁻¹) : R) * L) * ((↑a : R) * δ) = L * δ := by
  calc
    ((↑(a⁻¹) : R) * L) * ((↑a : R) * δ)
        = ((↑(a⁻¹) : R) * (↑a : R)) * (L * δ) := by
            ac_rfl
    _ = L * δ := by simp

theorem twoGaugeCovariance {R : Type*} [CommRing R]
    (a b : Rˣ) (L δ : R) :
    (((↑b : R) * (↑(a⁻¹) : R)) * L) * ((↑a : R) * δ)
      = (↑b : R) * (L * δ) := by
  calc
    (((↑b : R) * (↑(a⁻¹) : R)) * L) * ((↑a : R) * δ)
        = (↑b : R) * (((↑(a⁻¹) : R) * L) * ((↑a : R) * δ)) := by
            ac_rfl
    _ = (↑b : R) * (L * δ) := by rw [gaugeProductInvariant]

theorem ratioGaugeInvariant {K : Type*} [Field K]
    (a : Kˣ) (x y : K) (hy : y ≠ 0) :
    (((↑(a⁻¹) : K) * x) / ((↑(a⁻¹) : K) * y)) = x / y := by
  have ha : (↑(a⁻¹) : K) ≠ 0 := Units.ne_zero (a⁻¹)
  field_simp

theorem associatedGeneratorsNeedNotBeEqual :
    AssociatedByUnit (1 : ℚ) 2 ∧ (1 : ℚ) ≠ 2 := by
  constructor
  · refine ⟨Units.mk0 (2 : ℚ) (by norm_num), ?_⟩
    norm_num
  · norm_num

/-- One scalar specialization does not determine an ambient element: `1 + X`
evaluates to one at zero but is not the constant polynomial one. -/
theorem oneSpecializationDoesNotFixPolynomialElement :
    Polynomial.eval (0 : ℚ)
        ((1 : Polynomial ℚ) + Polynomial.X) = 1 ∧
      ((1 : Polynomial ℚ) + Polynomial.X) ≠ 1 := by
  constructor
  · simp
  · intro h
    have hx := congrArg (fun p : Polynomial ℚ => p.coeff 1) h
    norm_num at hx

#print axioms AssociatedByUnit
#print axioms associatedByUnit_refl
#print axioms associatedByUnit_symm
#print axioms associatedByUnit_trans
#print axioms unit_rescaling_associated
#print axioms gaugeProductInvariant
#print axioms twoGaugeCovariance
#print axioms ratioGaugeInvariant
#print axioms associatedGeneratorsNeedNotBeEqual
#print axioms oneSpecializationDoesNotFixPolynomialElement

end MillenniumBraid.BSDLineGauge
