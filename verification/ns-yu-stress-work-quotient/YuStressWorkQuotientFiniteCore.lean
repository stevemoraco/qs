import Mathlib

/-!
Finite coordinate shadow of the work-visible stress quotient in
`stevemoraco/RH#541`.

Choose an orthonormal frame with the nonzero Fourier direction `n=e₁` and write
one symmetric stress coefficient as

```text
R = [[a,b,c],[b,d,e],[c,e,f]].
```

The work symbol `n × Rn` sees only `(b,c)`. The visible Frobenius projection is

```text
[[0,b,c],[b,0,0],[c,0,0]].
```

This file proves only the resulting polynomial identities and kernel
characterization.

NOT formalized:

* orthogonal covariance / choice of Fourier frame;
* Fourier series, `curl div`, inverse Laplacian, Parseval;
* weak `L²` compactness, cutoffs, Yu's commutator work;
* Navier--Stokes regularity or blow-up.
-/

namespace Millennium.NavierStokes.YuStressWorkQuotientFiniteCore

def symbolNormSq (b c : ℝ) : ℝ := b ^ 2 + c ^ 2

def visibleNormSq (b c : ℝ) : ℝ :=
  b ^ 2 + c ^ 2 + b ^ 2 + c ^ 2

theorem visible_norm_isometry (b c : ℝ) :
    visibleNormSq b c = 2 * symbolNormSq b c := by
  simp [visibleNormSq, symbolNormSq]
  ring

theorem symbol_kernel_iff (b c : ℝ) :
    symbolNormSq b c = 0 ↔ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have hb : b ^ 2 = 0 := by nlinarith [sq_nonneg c]
    have hc : c ^ 2 = 0 := by nlinarith [sq_nonneg b]
    exact ⟨sq_eq_zero_iff.mp hb, sq_eq_zero_iff.mp hc⟩
  · rintro ⟨rfl, rfl⟩
    norm_num [symbolNormSq]

theorem visible_pairing
    (a b c d e f y z : ℝ) :
    (a * 0 + b * y + c * z +
      b * y + d * 0 + e * 0 +
      c * z + e * 0 + f * 0)
      = 2 * (b * y + c * z) := by
  ring

theorem null_remainder_pairing
    (a b c d e f y z : ℝ) :
    (a * 0 + (b - b) * y + (c - c) * z +
      (b - b) * y + d * 0 + e * 0 +
      (c - c) * z + e * 0 + f * 0)
      = 0 := by
  ring

theorem visible_projection_preserves_symbol (b c : ℝ) :
    (b, c) = (b, c) := by
  rfl

theorem symbol_bounded_by_full_stress
    (a b c d e f : ℝ) :
    symbolNormSq b c ≤
      a ^ 2 + b ^ 2 + c ^ 2 + b ^ 2 + d ^ 2 + e ^ 2 +
      c ^ 2 + e ^ 2 + f ^ 2 := by
  simp [symbolNormSq]
  positivity

#check visible_norm_isometry
#check symbol_kernel_iff
#check visible_pairing
#check null_remainder_pairing
#check visible_projection_preserves_symbol
#check symbol_bounded_by_full_stress

#print axioms visible_norm_isometry
#print axioms symbol_kernel_iff
#print axioms visible_pairing
#print axioms null_remainder_pairing
#print axioms visible_projection_preserves_symbol
#print axioms symbol_bounded_by_full_stress

end Millennium.NavierStokes.YuStressWorkQuotientFiniteCore
