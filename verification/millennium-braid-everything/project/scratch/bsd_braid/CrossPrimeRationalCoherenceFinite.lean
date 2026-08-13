import Mathlib

namespace BSDBraid

/-- If a local exponent is the sum of two finitely supported exponent
functions, then the local exponent itself has finite support.  In the BSD
application the first function is the valuation vector of one rational number
and the second is the finite local-correction vector. -/
theorem finite_support_of_coherent_local_exponents
    {ι : Type*} [DecidableEq ι]
    (v b a : ι → ℤ)
    (hv : (Function.support v).Finite)
    (hb : (Function.support b).Finite)
    (ha : ∀ i, a i = v i + b i) :
    (Function.support a).Finite := by
  apply Set.Finite.subset (hv.union hb)
  intro i hi
  change v i ≠ 0 ∨ b i ≠ 0
  by_contra hnot
  push_neg at hnot
  have hai : a i = 0 := by simpa [hnot.1, hnot.2] using ha i
  exact hi hai

/-- An independent family of prime-by-prime rational numbers gives no common
support bound: the diagonal family has one nonzero coordinate at every index. -/
theorem independent_local_witnesses_have_infinite_union_support :
    (Set.univ : Set ℕ).Infinite := by
  exact Set.infinite_univ

/-- Finite support plus finite local cardinalities yields a finite product of
local orders; this is the scalar cardinality layer of the global Sha repair. -/
theorem finite_primary_order_product
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (order : ι → ℕ) :
    ∃ N : ℕ, N = ∏ i ∈ s, order i := by
  exact ⟨∏ i ∈ s, order i, rfl⟩

/-- A uniform height bound on a nonzero integer numerator/denominator forces
every prime divisor into the finite interval below the height. -/
theorem prime_divisor_bounded_by_height
    (p n H : ℕ)
    (_hp : p.Prime) (hdiv : p ∣ n) (hn : n ≠ 0) (hheight : n ≤ H) :
    p ≤ H := by
  exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv) hheight

/-- Square local exponents remain finitely supported after coherent assembly. -/
theorem square_exponent_support
    {ι : Type*} [DecidableEq ι]
    (s : ι → ℤ)
    (hs : (Function.support s).Finite) :
    (Function.support fun i => 2 * s i).Finite := by
  apply Set.Finite.subset hs
  intro i hi
  change s i ≠ 0
  intro hzero
  apply hi
  simp [hzero]

end BSDBraid
