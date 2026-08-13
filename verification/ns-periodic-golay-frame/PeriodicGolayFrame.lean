import Mathlib

/-!
# Explicit periodic Golay translation frame

This file closes, on the finite cyclic group `Fin 8`, the bridge between an
explicit zero-padded length-four Golay pair and the finite matrix tight-frame
identity.

Rows are indexed by one of the two Golay species and by all eight cyclic
translations.  Their Gram matrix is exactly `8 I`, so analysis followed by
synthesis reconstructs every signal exactly with frame constant eight.

The three-dimensional tensor lift, Fourier lattice embedding, vector helical
symbol, Leray projection, leakage control, shell-model shadowing, and
Navier--Stokes breakdown are not proved here.
-/

namespace Millennium.NavierStokes.PeriodicGolayFrame

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

/-- The first Golay word, zero-padded from length four to the cyclic group of
order eight. -/
def wordA (n : Fin 8) : ℝ :=
  if n = 0 then 1
  else if n = 1 then 1
  else if n = 2 then 1
  else if n = 3 then -1
  else 0

/-- The second Golay word, zero-padded from length four to the cyclic group of
order eight. -/
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

/-- Direct finite certificate that the sixteen translated rows have Gram
matrix `8 I`. -/
theorem cyclicGolayKernel_gram_delta (a b : Fin 8) :
    frameGram cyclicGolayKernel a b = if a = b then 8 else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [frameGram, cyclicGolayKernel, wordA, wordB,
      Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]

/-- Exact periodic Golay translation-frame reconstruction on every signal on
`Fin 8`. -/
theorem cyclicGolay_reconstruction (f : Fin 8 → ℝ) (a : Fin 8) :
    ∑ r, cyclicGolayKernel r a * frameAnalysis cyclicGolayKernel f r =
      8 * f a := by
  exact deltaGram_reconstruction cyclicGolayKernel 8
    cyclicGolayKernel_gram_delta f a

#print axioms deltaGram_reconstruction
#print axioms cyclicGolayKernel_gram_delta
#print axioms cyclicGolay_reconstruction

end Millennium.NavierStokes.PeriodicGolayFrame
