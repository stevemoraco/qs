import Mathlib

namespace NSFullHelicityDecomposition

/-!
Finite algebra for the complete one-pump right-angle heterochiral linearization.
The state coordinates are `(a,b,c,D)` over `ℂ`, with `D = sqrt(2) d`.
No Fourier, Leray, Euler, Navier--Stokes, or Clay theorem is formalized here.
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

/-- The exact full-polarization linearization from the audited right-angle pump.
Its coordinates are
`a' = i c/2`, `b' = c/2 + i D/2`, `c' = 0`, `D' = a + i b`. -/
def M (x : State) : State :=
  ⟨Complex.I * x.c / 2,
   x.c / 2 + Complex.I * x.D / 2,
   0,
   x.a + Complex.I * x.b⟩

/-- Second iterate of the exact matrix. -/
def M2 (x : State) : State := M (M x)

/-- Third iterate of the exact matrix. -/
def M3 (x : State) : State := M (M2 x)

/-- Fourth iterate of the exact matrix. -/
def M4 (x : State) : State := M (M3 x)

/-- Scalar multiplication composes multiplicatively. -/
theorem scale_scale (z w : ℂ) (x : State) :
    scaleState z (scaleState w x) = scaleState (z * w) x := by
  ext <;> simp [scaleState] <;> ring

/-- The matrix commutes with scalar multiplication. -/
theorem M_scale (z : ℂ) (x : State) :
    M (scaleState z x) = scaleState z (M x) := by
  ext <;> simp [M, scaleState] <;> ring

/-- The exact matrix polynomial `2 M^4 + M^2 = 0`. -/
theorem matrix_polynomial (x : State) :
    addState (scaleState 2 (M4 x)) (M2 x) = zeroState := by
  ext <;> simp [addState, scaleState, M4, M3, M2, M, zeroState] <;> ring

/-- Every nonzero eigenvector has eigenvalue satisfying
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
        simpa [pow_two] using scale_scale lambda lambda x
  have h4 : M4 x = scaleState (lambda ^ 4) x := by
    calc
      M4 x = M2 (M2 x) := by
        simp [M4, M3, M2]
      _ = M2 (scaleState (lambda ^ 2) x) := by rw [h2]
      _ = scaleState (lambda ^ 2) (M2 x) := by
        simp only [M2]
        rw [M_scale, M_scale]
      _ = scaleState (lambda ^ 2) (scaleState (lambda ^ 2) x) := by rw [h2]
      _ = scaleState (lambda ^ 4) x := by
        simpa [pow_four] using scale_scale (lambda ^ 2) (lambda ^ 2) x
  have hzero := matrix_polynomial x
  rw [h4, h2] at hzero
  have hscaled : scaleState (2 * lambda ^ 4 + lambda ^ 2) x = zeroState := by
    simpa [addState, scaleState, zeroState] using hzero
  by_contra hpoly
  apply hx
  calc
    x = scaleState 1 x := by ext <;> simp [scaleState]
    _ = scaleState ((2 * lambda ^ 4 + lambda ^ 2)⁻¹ *
          (2 * lambda ^ 4 + lambda ^ 2)) x := by
      rw [inv_mul_cancel₀ hpoly]
    _ = scaleState (2 * lambda ^ 4 + lambda ^ 2)⁻¹
          (scaleState (2 * lambda ^ 4 + lambda ^ 2) x) := by
      rw [scale_scale]
    _ = scaleState (2 * lambda ^ 4 + lambda ^ 2)⁻¹ zeroState := by rw [hscaled]
    _ = zeroState := by ext <;> simp [scaleState, zeroState]

/-- The full matrix has no nonzero real eigenvalue. -/
theorem real_eigenvalue_zero
    {x : State} (hx : x ≠ zeroState) {lambda : ℝ}
    (heigen : M x = scaleState (lambda : ℂ) x) :
    lambda = 0 := by
  have hc := eigenvalue_polynomial hx heigen
  have hr : 2 * lambda ^ 4 + lambda ^ 2 = 0 := by
    simpa using congrArg Complex.re hc
  nlinarith [sq_nonneg lambda, sq_nonneg (lambda ^ 2)]

/-- Projection onto the oscillatory generalized eigenspace. -/
def P (x : State) : State := scaleState (-2) (M2 x)

/-- Nilpotent zero-mode part. -/
def N (x : State) : State :=
  addState (M x) (scaleState 2 (M3 x))

/-- Oscillatory part. -/
def K (x : State) : State := scaleState (-2) (M3 x)

/-- Exact decomposition `M = N + K`. -/
theorem nilpotent_oscillator_split (x : State) :
    addState (N x) (K x) = M x := by
  ext <;> simp [N, K, addState, scaleState, M3, M2, M] <;> ring

/-- `P` is an exact projection. -/
theorem projection_idempotent (x : State) :
    P (P x) = P x := by
  ext <;> simp [P, scaleState, M2, M] <;> ring

/-- The zero-mode part is nilpotent of order two. -/
theorem nilpotent_square_zero (x : State) :
    N (N x) = zeroState := by
  ext <;> simp [N, addState, scaleState, M3, M2, M, zeroState] <;> ring

/-- The oscillator obeys `2 K^2 + P = 0`, i.e. frequency squared `1/2`
on the projected sector. -/
theorem oscillator_square (x : State) :
    addState (scaleState 2 (K (K x))) (P x) = zeroState := by
  ext <;> simp [K, P, addState, scaleState, M3, M2, M, zeroState] <;> ring

/-- The nilpotent and oscillator sectors do not feed one another. -/
theorem nilpotent_after_oscillator (x : State) :
    N (K x) = zeroState := by
  ext <;> simp [N, K, addState, scaleState, M3, M2, M, zeroState] <;> ring

/-- The opposite composition also vanishes. -/
theorem oscillator_after_nilpotent (x : State) :
    K (N x) = zeroState := by
  ext <;> simp [N, K, addState, scaleState, M3, M2, M, zeroState] <;> ring

/-- A concrete generalized zero-mode seed. -/
def jordanSeed : State := ⟨0, 0, 2, 4 * Complex.I⟩

/-- Its first image is nonzero but lies in the kernel. -/
def jordanVector : State := ⟨Complex.I, -1, 0, 0⟩

/-- Exact first Jordan step. -/
theorem jordan_first_step : M jordanSeed = jordanVector := by
  ext <;> simp [M, jordanSeed, jordanVector] <;> ring

/-- Exact second Jordan step. -/
theorem jordan_second_step : M jordanVector = zeroState := by
  ext <;> simp [M, jordanVector, zeroState] <;> ring

/-- The generalized zero mode is genuinely nontrivial. -/
theorem jordan_vector_nonzero : jordanVector ≠ zeroState := by
  intro h
  have hb := congrArg State.b h
  norm_num [jordanVector, zeroState] at hb

#check matrix_polynomial
#print axioms scale_scale
#print axioms M_scale
#print axioms matrix_polynomial
#print axioms eigenvalue_polynomial
#print axioms real_eigenvalue_zero
#print axioms nilpotent_oscillator_split
#print axioms projection_idempotent
#print axioms nilpotent_square_zero
#print axioms oscillator_square
#print axioms nilpotent_after_oscillator
#print axioms oscillator_after_nilpotent
#print axioms jordan_first_step
#print axioms jordan_second_step
#print axioms jordan_vector_nonzero

end NSFullHelicityDecomposition
