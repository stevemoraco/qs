import Mathlib

/-!
# Explicit three-dimensional periodic Golay translation frame

This standalone finite file proves that tensoring the zero-padded length-four
Golay pair in three cyclic coordinates gives an exact eight-species
translation frame on `(Fin 8)^3` with Gram matrix `512 I`.

The proof contains the explicit one-dimensional finite certificate, a generic
Kronecker-product Gram factorization, the two- and three-dimensional delta
Gram theorems, and exact analysis--synthesis reconstruction.

No Fourier embedding, divergence-free polarization, Leray projection,
Navier--Stokes symbol matching, leakage estimate, shell-model shadowing, or
finite-time breakdown is formalized here.
-/

namespace Millennium.NavierStokes.PeriodicGolayFrame3D

section FiniteFrame

variable {ρ κ : Type*} [Fintype ρ] [Fintype κ] [DecidableEq κ]

/-- Analysis coefficient of a finite real matrix. -/
def frameAnalysis (K : ρ → κ → ℝ) (f : κ → ℝ) (r : ρ) : ℝ :=
  ∑ x, K r x * f x

/-- Gram entry of a finite real matrix. -/
def frameGram (K : ρ → κ → ℝ) (a b : κ) : ℝ :=
  ∑ r, K r a * K r b

/-- A delta Gram matrix gives exact analysis--synthesis reconstruction. -/
theorem deltaGram_reconstruction
    (K : ρ → κ → ℝ) (C : ℝ)
    (hGram : ∀ a b, frameGram K a b = if a = b then C else 0)
    (f : κ → ℝ) (a : κ) :
    ∑ r, K r a * frameAnalysis K f r = C * f a := by
  classical
  unfold frameAnalysis frameGram
  calc
    (∑ r, K r a * (∑ b, K r b * f b))
        = ∑ r, ∑ b, K r a * (K r b * f b) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
    _ = ∑ b, ∑ r, K r a * (K r b * f b) := by
          rw [Finset.sum_comm]
    _ = ∑ b, (∑ r, K r a * K r b) * f b := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r hr
          ring
    _ = ∑ b, (if a = b then C else 0) * f b := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [hGram a b]
    _ = C * f a := by simp

end FiniteFrame

/-- Kronecker product of two finite real kernels. -/
def tensorKernel
    {ρ₁ κ₁ ρ₂ κ₂ : Type*}
    (K₁ : ρ₁ → κ₁ → ℝ) (K₂ : ρ₂ → κ₂ → ℝ)
    (r : ρ₁ × ρ₂) (x : κ₁ × κ₂) : ℝ :=
  K₁ r.1 x.1 * K₂ r.2 x.2

/-- The Gram matrix of a Kronecker-product kernel is the product of the two
factor Gram matrices. -/
theorem frameGram_tensorKernel
    {ρ₁ κ₁ ρ₂ κ₂ : Type*}
    [Fintype ρ₁] [Fintype κ₁] [Fintype ρ₂] [Fintype κ₂]
    (K₁ : ρ₁ → κ₁ → ℝ) (K₂ : ρ₂ → κ₂ → ℝ)
    (a b : κ₁ × κ₂) :
    frameGram (tensorKernel K₁ K₂) a b =
      frameGram K₁ a.1 b.1 * frameGram K₂ a.2 b.2 := by
  classical
  unfold frameGram tensorKernel
  rw [Fintype.sum_prod_type]
  calc
    (∑ r₁, ∑ r₂,
        (K₁ r₁ a.1 * K₂ r₂ a.2) * (K₁ r₁ b.1 * K₂ r₂ b.2))
        = ∑ r₁, (K₁ r₁ a.1 * K₁ r₁ b.1) *
            (∑ r₂, K₂ r₂ a.2 * K₂ r₂ b.2) := by
          apply Finset.sum_congr rfl
          intro r₁ hr₁
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r₂ hr₂
          ring
    _ = (∑ r₁, K₁ r₁ a.1 * K₁ r₁ b.1) *
          (∑ r₂, K₂ r₂ a.2 * K₂ r₂ b.2) := by
          rw [Finset.sum_mul]

/-- Tensor products preserve the delta-Gram property and multiply the frame
constants. -/
theorem tensorKernel_gram_delta
    {ρ₁ κ₁ ρ₂ κ₂ : Type*}
    [Fintype ρ₁] [Fintype κ₁] [Fintype ρ₂] [Fintype κ₂]
    [DecidableEq κ₁] [DecidableEq κ₂]
    (K₁ : ρ₁ → κ₁ → ℝ) (K₂ : ρ₂ → κ₂ → ℝ)
    (C₁ C₂ : ℝ)
    (h₁ : ∀ a b, frameGram K₁ a b = if a = b then C₁ else 0)
    (h₂ : ∀ a b, frameGram K₂ a b = if a = b then C₂ else 0)
    (a b : κ₁ × κ₂) :
    frameGram (tensorKernel K₁ K₂) a b =
      if a = b then C₁ * C₂ else 0 := by
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  rw [frameGram_tensorKernel]
  rw [h₁ a₁ b₁, h₂ a₂ b₂]
  by_cases e₁ : a₁ = b₁ <;>
    by_cases e₂ : a₂ = b₂ <;>
      simp [e₁, e₂]

/-- First Golay word, zero-padded to the cyclic group of order eight. -/
def wordA (n : Fin 8) : ℝ :=
  if n = 0 then 1
  else if n = 1 then 1
  else if n = 2 then 1
  else if n = 3 then -1
  else 0

/-- Second Golay word, zero-padded to the cyclic group of order eight. -/
def wordB (n : Fin 8) : ℝ :=
  if n = 0 then 1
  else if n = 1 then 1
  else if n = 2 then -1
  else if n = 3 then 1
  else 0

/-- Two species and all cyclic translations of the explicit Golay pair. -/
def cyclicGolayKernel (r : Bool × Fin 8) (x : Fin 8) : ℝ :=
  match r.1 with
  | false => wordA (x - r.2)
  | true => wordB (x - r.2)

/-- The explicit one-dimensional translated Golay rows have Gram `8 I`. -/
theorem cyclicGolayKernel_gram_delta (a b : Fin 8) :
    frameGram cyclicGolayKernel a b = if a = b then 8 else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [frameGram, cyclicGolayKernel, wordA, wordB,
      Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]

abbrev Row1 := Bool × Fin 8
abbrev Site2 := Fin 8 × Fin 8
abbrev Row2 := Row1 × Row1

/-- Four species and all translations in two cyclic coordinates. -/
def cyclicGolayKernel2D : Row2 → Site2 → ℝ :=
  tensorKernel cyclicGolayKernel cyclicGolayKernel

/-- Exact two-dimensional Gram identity `8² I = 64 I`. -/
theorem cyclicGolayKernel2D_gram_delta (a b : Site2) :
    frameGram cyclicGolayKernel2D a b = if a = b then 64 else 0 := by
  simpa [cyclicGolayKernel2D] using
    (tensorKernel_gram_delta cyclicGolayKernel cyclicGolayKernel
      8 8 cyclicGolayKernel_gram_delta cyclicGolayKernel_gram_delta a b)

abbrev Site3 := Fin 8 × Site2
abbrev Row3 := Row1 × Row2

/-- Eight species and all translations in three cyclic coordinates. -/
def cyclicGolayKernel3D : Row3 → Site3 → ℝ :=
  tensorKernel cyclicGolayKernel cyclicGolayKernel2D

/-- Exact three-dimensional Gram identity `8³ I = 512 I`. -/
theorem cyclicGolayKernel3D_gram_delta (a b : Site3) :
    frameGram cyclicGolayKernel3D a b = if a = b then 512 else 0 := by
  simpa [cyclicGolayKernel3D] using
    (tensorKernel_gram_delta cyclicGolayKernel cyclicGolayKernel2D
      8 64 cyclicGolayKernel_gram_delta cyclicGolayKernel2D_gram_delta a b)

/-- Exact analysis--synthesis reconstruction for every real signal on the
three-dimensional cyclic box. -/
theorem cyclicGolay3D_reconstruction (f : Site3 → ℝ) (a : Site3) :
    ∑ r, cyclicGolayKernel3D r a * frameAnalysis cyclicGolayKernel3D f r =
      512 * f a := by
  exact deltaGram_reconstruction cyclicGolayKernel3D 512
    cyclicGolayKernel3D_gram_delta f a

#print axioms deltaGram_reconstruction
#print axioms frameGram_tensorKernel
#print axioms tensorKernel_gram_delta
#print axioms cyclicGolayKernel_gram_delta
#print axioms cyclicGolayKernel2D_gram_delta
#print axioms cyclicGolayKernel3D_gram_delta
#print axioms cyclicGolay3D_reconstruction

end Millennium.NavierStokes.PeriodicGolayFrame3D
