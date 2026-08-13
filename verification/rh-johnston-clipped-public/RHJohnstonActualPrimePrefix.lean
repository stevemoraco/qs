import Mathlib.NumberTheory.Chebyshev

open Finset Real
open scoped Nat.Prime

namespace RHJohnstonActualPrimePrefix

/-- Mathlib's real Chebyshev theta restricted to natural cutoffs.  Naming this
wrapper prevents coercion normalization from obscuring exact integer updates. -/
noncomputable def thetaNat (n : ℕ) : ℝ := Chebyshev.theta (n : ℝ)

/-- The weighted prime prefix `W(n)=sum_{p≤n} p log p` appearing after
eliminating Johnston's integral by summation by parts. -/
noncomputable def weightedPrimeSum (n : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE n, (p : ℝ) * log p

/-- The exact discrete Johnston energy at an integer cutoff. -/
noncomputable def prefixEnergy (n : ℕ) : ℝ :=
  weightedPrimeSum n - (thetaNat n) ^ 2 / 2 - 2

/-- The weighted prefix changes only when `n+1` is prime. -/
theorem weightedPrimeSum_succ (n : ℕ) :
    weightedPrimeSum (n + 1) =
      if (n + 1).Prime then
        weightedPrimeSum n + ((n + 1 : ℕ) : ℝ) * log ((n + 1 : ℕ) : ℝ)
      else weightedPrimeSum n := by
  unfold weightedPrimeSum
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [sum_insert (Nat.notMem_primesLE n)]
    ac_rfl
  · rfl

/-- Mathlib's Chebyshev theta has the same exact one-integer update law. -/
theorem thetaNat_succ (n : ℕ) :
    thetaNat (n + 1) =
      if (n + 1).Prime then
        thetaNat n + log ((n + 1 : ℕ) : ℝ)
      else thetaNat n := by
  unfold thetaNat
  rw [Chebyshev.theta_eq_sum_primesLE_log (n + 1),
      Chebyshev.theta_eq_sum_primesLE_log n]
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [sum_insert (Nat.notMem_primesLE n)]
  · rfl

/-- At a genuine prime arrival `q=n+1`, the actual mathlib-defined prime
prefix energy obeys the abstract recurrence exactly. -/
theorem prefixEnergy_succ_of_prime
    {n : ℕ} (hprime : (n + 1).Prime) :
    prefixEnergy (n + 1) - prefixEnergy n =
      log (((n + 1 : ℕ) : ℝ)) *
          (((n + 1 : ℕ) : ℝ) - thetaNat n) -
        (log (((n + 1 : ℕ) : ℝ))) ^ 2 / 2 := by
  unfold prefixEnergy
  rw [weightedPrimeSum_succ, thetaNat_succ]
  simp only [if_pos hprime]
  ring

/-- At a composite arrival, both prime prefixes and hence the energy are
unchanged. -/
theorem prefixEnergy_succ_of_not_prime
    {n : ℕ} (hcomp : ¬(n + 1).Prime) :
    prefixEnergy (n + 1) = prefixEnergy n := by
  unfold prefixEnergy
  rw [weightedPrimeSum_succ, thetaNat_succ]
  simp [hcomp]

/-- Exact dichotomy for every integer step. -/
theorem prefixEnergy_succ (n : ℕ) :
    prefixEnergy (n + 1) - prefixEnergy n =
      if (n + 1).Prime then
        log (((n + 1 : ℕ) : ℝ)) *
            (((n + 1 : ℕ) : ℝ) - thetaNat n) -
          (log (((n + 1 : ℕ) : ℝ))) ^ 2 / 2
      else 0 := by
  by_cases h : (n + 1).Prime
  · rw [if_pos h, prefixEnergy_succ_of_prime h]
  · rw [if_neg h, prefixEnergy_succ_of_not_prime h]
    ring

#print axioms weightedPrimeSum_succ
#print axioms thetaNat_succ
#print axioms prefixEnergy_succ_of_prime
#print axioms prefixEnergy_succ_of_not_prime
#print axioms prefixEnergy_succ

end RHJohnstonActualPrimePrefix
