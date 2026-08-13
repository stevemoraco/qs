import Mathlib

namespace NSFullHelicityDecomposition

noncomputable section
set_option linter.unusedSimpArgs false

/-!
Finite algebra for the complete-polarization two-frequency truncation of the
right-angle heterochiral linearization on carriers `p` and `p+q`.
The state coordinates are `(a,b,c,D)` over `ℂ`, with `D = sqrt(2) d`.
The companion `NSOnePumpSidebandFirewall` proves that a real pump also forces
`p-q`, so this is not the full sideband-chain linearization.
No Fourier-series, Euler, Navier--Stokes, or Clay theorem is formalized here.
-/

@[ext]
structure State where
  a : ℂ
  b : ℂ
  c : ℂ
  D : ℂ

/-- Zero state. -/
def zeroState : State := ⟨0, 0, 0, 0⟩

/-- Coordinatewise addition. -/
def addState (x y : State) : State :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.D + y.D⟩

/-- Coordinatewise complex scalar multiplication. -/
def scaleState (z : ℂ) (x : State) : State :=
  ⟨z * x.a, z * x.b, z * x.c, z * x.D⟩

/-- The exact complete-polarization map inside the two-frequency truncation:
`a' = i c/2`, `b' = c/2 + i D/2`, `c' = 0`, `D' = a + i b`. -/
def M (x : State) : State :=
  ⟨Complex.I * x.c / 2,
   x.c / 2 + Complex.I * x.D / 2,
   0,
   x.a + Complex.I * x.b⟩

/-- Second iterate. -/
def M2 (x : State) : State := M (M x)

/-- Third iterate. -/
def M3 (x : State) : State := M (M2 x)

/-- Fourth iterate. -/
def M4 (x : State) : State := M (M3 x)

/-- Scalar multiplication composes multiplicatively. -/
theorem scale_scale (z w : ℂ) (x : State) :
    scaleState z (scaleState w x) = scaleState (z * w) x := by
  ext <;> dsimp [scaleState] <;> ring

/-- The truncated matrix commutes with scalar multiplication. -/
theorem M_scale (z : ℂ) (x : State) :
    M (scaleState z x) = scaleState z (M x) := by
  ext <;> dsimp [M, scaleState] <;> ring

/-- Exact coordinate formula for the second iterate. -/
theorem M2_formula (x : State) :
    M2 x = ⟨0, Complex.I * x.a / 2 - x.b / 2,
      0, -x.D / 2 + Complex.I * x.c⟩ := by
  ext <;> simp [M2, M, Complex.I_mul_I] <;> ring

/-- Exact coordinate formula for the third iterate. -/
theorem M3_formula (x : State) :
    M3 x = ⟨0, -Complex.I * x.D / 4 - x.c / 2,
      0, -x.a / 2 - Complex.I * x.b / 2⟩ := by
  ext <;> simp [M3, M2, M, Complex.I_mul_I] <;> ring

/-- Exact coordinate formula for the fourth iterate. -/
theorem M4_formula (x : State) :
    M4 x = ⟨0, -Complex.I * x.a / 4 + x.b / 4,
      0, x.D / 4 - Complex.I * x.c / 2⟩ := by
  ext <;> simp [M4, M3, M2, M, Complex.I_mul_I] <;> ring

/-- The exact matrix polynomial `2 M^4 + M^2 = 0`. -/
theorem matrix_polynomial (x : State) :
    addState (scaleState 2 (M4 x)) (M2 x) = zeroState := by
  rw [M4_formula, M2_formula]
  ext <;> dsimp [addState, scaleState, zeroState] <;> ring

/-- A nonzero eigenvector forces its eigenvalue to satisfy
`2 lambda^4 + lambda^2 = 0`. -/
theorem eigenvalue_polynomial
    {x : State} (hx : x ≠ zeroState) {lambda : ℂ}
    (heigen : M x = scaleState lambda x) :
    2 * lambda ^ 4 + lambda ^ 2 = 0 := by
  have h2 : M2 x = scaleState (lambda ^ 2) x := by
    calc
      M2 x = M (M x) := rfl
      _ = M (scaleState lambda x) := by rw [heigen]
      _ = scaleState lambda (M x) := M_scale lambda x
      _ = scaleState lambda (scaleState lambda x) := by rw [heigen]
      _ = scaleState (lambda ^ 2) x := by
        ext <;> dsimp [scaleState] <;> ring
  have h3 : M3 x = scaleState (lambda ^ 3) x := by
    calc
      M3 x = M (M2 x) := rfl
      _ = M (scaleState (lambda ^ 2) x) := by rw [h2]
      _ = scaleState (lambda ^ 2) (M x) := M_scale (lambda ^ 2) x
      _ = scaleState (lambda ^ 2) (scaleState lambda x) := by rw [heigen]
      _ = scaleState (lambda ^ 3) x := by
        ext <;> dsimp [scaleState] <;> ring
  have h4 : M4 x = scaleState (lambda ^ 4) x := by
    calc
      M4 x = M (M3 x) := rfl
      _ = M (scaleState (lambda ^ 3) x) := by rw [h3]
      _ = scaleState (lambda ^ 3) (M x) := M_scale (lambda ^ 3) x
      _ = scaleState (lambda ^ 3) (scaleState lambda x) := by rw [heigen]
      _ = scaleState (lambda ^ 4) x := by
        ext <;> dsimp [scaleState] <;> ring
  have hz := matrix_polynomial x
  rw [h4, h2] at hz
  let z : ℂ := 2 * lambda ^ 4 + lambda ^ 2
  have hscaled : scaleState z x = zeroState := by
    have ha := congrArg State.a hz
    have hb := congrArg State.b hz
    have hc := congrArg State.c hz
    have hD := congrArg State.D hz
    ext
    · dsimp [z, addState, scaleState, zeroState] at ha ⊢
      calc
        (2 * lambda ^ 4 + lambda ^ 2) * x.a =
            2 * (lambda ^ 4 * x.a) + lambda ^ 2 * x.a := by ring
        _ = 0 := ha
    · dsimp [z, addState, scaleState, zeroState] at hb ⊢
      calc
        (2 * lambda ^ 4 + lambda ^ 2) * x.b =
            2 * (lambda ^ 4 * x.b) + lambda ^ 2 * x.b := by ring
        _ = 0 := hb
    · dsimp [z, addState, scaleState, zeroState] at hc ⊢
      calc
        (2 * lambda ^ 4 + lambda ^ 2) * x.c =
            2 * (lambda ^ 4 * x.c) + lambda ^ 2 * x.c := by ring
        _ = 0 := hc
    · dsimp [z, addState, scaleState, zeroState] at hD ⊢
      calc
        (2 * lambda ^ 4 + lambda ^ 2) * x.D =
            2 * (lambda ^ 4 * x.D) + lambda ^ 2 * x.D := by ring
        _ = 0 := hD
  by_contra hpoly
  apply hx
  have hz0 : z ≠ 0 := by simpa [z] using hpoly
  have ha := congrArg State.a hscaled
  have hb := congrArg State.b hscaled
  have hc := congrArg State.c hscaled
  have hD := congrArg State.D hscaled
  ext
  · dsimp [scaleState, zeroState] at ha
    exact (mul_eq_zero.mp ha).resolve_left hz0
  · dsimp [scaleState, zeroState] at hb
    exact (mul_eq_zero.mp hb).resolve_left hz0
  · dsimp [scaleState, zeroState] at hc
    exact (mul_eq_zero.mp hc).resolve_left hz0
  · dsimp [scaleState, zeroState] at hD
    exact (mul_eq_zero.mp hD).resolve_left hz0

/-- Algebraic factorization of the eigenvalue polynomial. -/
theorem root_classification {lambda : ℂ}
    (h : 2 * lambda ^ 4 + lambda ^ 2 = 0) :
    lambda = 0 ∨ 2 * lambda ^ 2 + 1 = 0 := by
  have hf : lambda ^ 2 * (2 * lambda ^ 2 + 1) = 0 := by
    calc
      lambda ^ 2 * (2 * lambda ^ 2 + 1) =
          2 * lambda ^ 4 + lambda ^ 2 := by ring
      _ = 0 := h
  rcases mul_eq_zero.mp hf with hsq | hquad
  · left
    have hmul : lambda * lambda = 0 := by simpa [pow_two] using hsq
    rcases mul_eq_zero.mp hmul with hzero | hzero
    · exact hzero
    · exact hzero
  · right
    exact hquad

/-- Every root of `2 lambda^2 + 1` has zero real part. -/
theorem quadratic_root_real_part_zero {lambda : ℂ}
    (h : 2 * lambda ^ 2 + 1 = 0) :
    lambda.re = 0 := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [pow_two] at hr hi
  by_cases hre : lambda.re = 0
  · exact hre
  · have hprod : lambda.re * lambda.im = 0 := by nlinarith [hi]
    have him : lambda.im = 0 := (mul_eq_zero.mp hprod).resolve_left hre
    rw [him] at hr
    nlinarith [sq_nonneg lambda.re]

/-- Every eigenvalue of the two-frequency truncation has zero real part. -/
theorem eigenvalue_real_part_zero
    {x : State} (hx : x ≠ zeroState) {lambda : ℂ}
    (heigen : M x = scaleState lambda x) :
    lambda.re = 0 := by
  rcases root_classification (eigenvalue_polynomial hx heigen) with hzero | hquad
  · simp [hzero]
  · exact quadratic_root_real_part_zero hquad

/-- Exact polynomial projection onto the oscillator sector. -/
def P (x : State) : State :=
  ⟨0, x.b - Complex.I * x.a, 0, x.D - 2 * Complex.I * x.c⟩

/-- Exact nilpotent zero-mode part. -/
def N (x : State) : State :=
  ⟨Complex.I * x.c / 2, -x.c / 2, 0, 0⟩

/-- Exact oscillator part. -/
def K (x : State) : State :=
  ⟨0, x.c + Complex.I * x.D / 2, 0, x.a + Complex.I * x.b⟩

/-- `P` equals `-2 M^2`. -/
theorem projection_is_polynomial (x : State) :
    P x = scaleState (-2) (M2 x) := by
  rw [M2_formula]
  ext <;> simp [P, scaleState] <;> ring

/-- `N` equals `M + 2 M^3`. -/
theorem nilpotent_is_polynomial (x : State) :
    N x = addState (M x) (scaleState 2 (M3 x)) := by
  rw [M3_formula]
  ext <;> simp [N, M, addState, scaleState, Complex.I_mul_I] <;> ring

/-- `K` equals `-2 M^3`. -/
theorem oscillator_is_polynomial (x : State) :
    K x = scaleState (-2) (M3 x) := by
  rw [M3_formula]
  ext <;> simp [K, scaleState] <;> ring

/-- Exact decomposition `M = N + K`. -/
theorem nilpotent_oscillator_split (x : State) :
    addState (N x) (K x) = M x := by
  ext <;> simp [N, K, M, addState, Complex.I_mul_I] <;> ring

/-- `P` is an exact projection. -/
theorem projection_idempotent (x : State) :
    P (P x) = P x := by
  ext <;> simp [P, Complex.I_mul_I] <;> ring

/-- The zero-mode part is nilpotent of order two. -/
theorem nilpotent_square_zero (x : State) :
    N (N x) = zeroState := by
  ext <;> simp [N, zeroState]

/-- The oscillator obeys `2 K^2 + P = 0`. -/
theorem oscillator_square (x : State) :
    addState (scaleState 2 (K (K x))) (P x) = zeroState := by
  ext <;> simp [K, P, addState, scaleState, zeroState, Complex.I_mul_I] <;> ring

/-- The nilpotent sector vanishes after the oscillator sector. -/
theorem nilpotent_after_oscillator (x : State) :
    N (K x) = zeroState := by
  ext <;> simp [N, K, zeroState]

/-- The oscillator sector vanishes after the nilpotent sector. -/
theorem oscillator_after_nilpotent (x : State) :
    K (N x) = zeroState := by
  ext <;> simp [N, K, zeroState, Complex.I_mul_I] <;> ring

/-- A concrete generalized zero-mode seed. -/
def jordanSeed : State := ⟨0, 0, 2, 4 * Complex.I⟩

/-- Its nonzero image in the kernel. -/
def jordanVector : State := ⟨Complex.I, -1, 0, 0⟩

/-- Exact first Jordan step. -/
theorem jordan_first_step : M jordanSeed = jordanVector := by
  ext <;> simp [M, jordanSeed, jordanVector, Complex.I_mul_I] <;> ring

/-- Exact second Jordan step. -/
theorem jordan_second_step : M jordanVector = zeroState := by
  ext <;> simp [M, jordanVector, zeroState, Complex.I_mul_I] <;> ring

/-- The generalized zero mode is genuinely nontrivial. -/
theorem jordan_vector_nonzero : jordanVector ≠ zeroState := by
  intro h
  have hb := congrArg State.b h
  norm_num [jordanVector, zeroState] at hb

#print axioms scale_scale
#print axioms M_scale
#print axioms M2_formula
#print axioms M3_formula
#print axioms M4_formula
#print axioms matrix_polynomial
#print axioms eigenvalue_polynomial
#print axioms root_classification
#print axioms quadratic_root_real_part_zero
#print axioms eigenvalue_real_part_zero
#print axioms projection_is_polynomial
#print axioms nilpotent_is_polynomial
#print axioms oscillator_is_polynomial
#print axioms nilpotent_oscillator_split
#print axioms projection_idempotent
#print axioms nilpotent_square_zero
#print axioms oscillator_square
#print axioms nilpotent_after_oscillator
#print axioms oscillator_after_nilpotent
#print axioms jordan_first_step
#print axioms jordan_second_step
#print axioms jordan_vector_nonzero

end
end NSFullHelicityDecomposition
