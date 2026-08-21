import Mathlib

/-!
# Yang--Mills C456C: finite cut-dual and quantitative left-inverse core

This file formalizes only the abstract finite linear-algebra shell used by the
human C456C source theorem.

A family of rows `row : E → V` and linear cut functionals
`cut : E → (V →ₗ[𝕜] 𝕜)` is biorthogonal when

`cut e (row f) = if e = f then 1 else 0`.

The kernel-checked consequences are:

* cut analysis after row synthesis is the identity;
* row synthesis is injective, hence no nontrivial row relation exists;
* duplicate rows cannot possess a cut dual;
* any norm bound on a left inverse yields the corresponding singular-floor
  inequality.

The file does not formalize lattice blocks, paths, path-incidence numbers,
polar projection, `SU(N)`, Faizal--Shabir, gauge fixing, conditional measures,
Yang--Mills, a mass gap, or any Clay theorem.
-/

noncomputable section

namespace Millennium.YangMills.C456C

section AlgebraicCutDual

variable {𝕜 E V : Type*}
variable [Field 𝕜] [Fintype E] [DecidableEq E]
variable [AddCommGroup V] [Module 𝕜 V]

/-- Synthesize a vector from the finite row family. -/
def synth (row : E → V) (x : E → 𝕜) : V :=
  ∑ e, x e • row e

/-- Analyze a vector with the finite family of cut functionals. -/
def analyze (cut : E → (V →ₗ[𝕜] 𝕜)) (v : V) : E → 𝕜 :=
  fun e => cut e v

/-- A biorthogonal cut family recovers every coefficient after synthesis. -/
theorem analyze_synth_eq
    (row : E → V) (cut : E → (V →ₗ[𝕜] 𝕜))
    (hdual : ∀ e f, cut e (row f) = if e = f then 1 else 0)
    (x : E → 𝕜) :
    analyze cut (synth row x) = x := by
  funext e
  simp [analyze, synth, hdual]

/-- The cut analysis map is a left inverse of row synthesis. -/
theorem cutDual_leftInverse
    (row : E → V) (cut : E → (V →ₗ[𝕜] 𝕜))
    (hdual : ∀ e f, cut e (row f) = if e = f then 1 else 0) :
    Function.LeftInverse (analyze cut) (synth row) := by
  intro x
  exact analyze_synth_eq row cut hdual x

/-- A family admitting a cut dual has injective synthesis. -/
theorem synth_injective
    (row : E → V) (cut : E → (V →ₗ[𝕜] 𝕜))
    (hdual : ∀ e f, cut e (row f) = if e = f then 1 else 0) :
    Function.Injective (synth (𝕜 := 𝕜) row) :=
  (cutDual_leftInverse row cut hdual).injective

/-- Equivalently, every finite coefficient relation is trivial. -/
theorem coefficients_eq_zero
    (row : E → V) (cut : E → (V →ₗ[𝕜] 𝕜))
    (hdual : ∀ e f, cut e (row f) = if e = f then 1 else 0)
    (x : E → 𝕜)
    (hzero : synth row x = 0) :
    x = 0 := by
  apply synth_injective (𝕜 := 𝕜) row cut hdual
  simpa [synth] using hzero

/-- Distinct indices with identical rows cannot possess a Kronecker cut dual. -/
omit [Fintype E] in
theorem duplicate_rows_forbid_cutDual
    (row : E → V) (cut : E → (V →ₗ[𝕜] 𝕜))
    (hdual : ∀ e f, cut e (row f) = if e = f then 1 else 0)
    {e f : E} (hne : e ≠ f) (hrow : row e = row f) :
    False := by
  have he : cut e (row e) = 1 := by
    simpa using hdual e e
  have hf : cut e (row f) = 0 := by
    simpa [hne] using hdual e f
  have hone : (1 : 𝕜) = 0 := by
    calc
      (1 : 𝕜) = cut e (row e) := he.symm
      _ = cut e (row f) := by rw [hrow]
      _ = 0 := hf
  exact one_ne_zero hone

end AlgebraicCutDual

section QuantitativeLeftInverse

variable {X Y : Type*}
variable [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]

/--
If `C` is a left inverse of `A` and has operator bound `K`, then `A` has the
corresponding lower norm bound.  In C456C, `A` is row synthesis,
`C` is interface-cut analysis, and `K = sqrt q_max`.
-/
theorem norm_lower_bound_of_leftInverse
    (A : X → Y) (C : Y → X)
    (hleft : Function.LeftInverse C A)
    {K : ℝ} (hK : 0 < K)
    (hbound : ∀ y, ‖C y‖ ≤ K * ‖y‖)
    (x : X) :
    ‖x‖ / K ≤ ‖A x‖ := by
  apply (div_le_iff₀ hK).2
  calc
    ‖x‖ = ‖C (A x)‖ := by rw [hleft x]
    _ ≤ K * ‖A x‖ := hbound (A x)
    _ = ‖A x‖ * K := mul_comm _ _

/-- Square-root specialization matching the interface-size bound. -/
theorem norm_lower_bound_of_sqrt_leftInverse
    (A : X → Y) (C : Y → X)
    (hleft : Function.LeftInverse C A)
    {q : ℝ} (hq : 0 < q)
    (hbound : ∀ y, ‖C y‖ ≤ Real.sqrt q * ‖y‖)
    (x : X) :
    ‖x‖ / Real.sqrt q ≤ ‖A x‖ :=
  norm_lower_bound_of_leftInverse A C hleft (Real.sqrt_pos.2 hq) hbound x

end QuantitativeLeftInverse

#print axioms analyze_synth_eq
#print axioms cutDual_leftInverse
#print axioms synth_injective
#print axioms coefficients_eq_zero
#print axioms duplicate_rows_forbid_cutDual
#print axioms norm_lower_bound_of_leftInverse
#print axioms norm_lower_bound_of_sqrt_leftInverse

end Millennium.YangMills.C456C
