import Mathlib

/-!
# Exact 3--4--5 lattice recursion firewall

The displayed self-similar mixed-helicity relay uses the exact scale recurrence

  4 * N (k+1) = 5 * N k.

This file proves that a depth-`r` natural-number chain forces `4^r ∣ N 0`,
and hence an infinite chain is necessarily the zero chain.  The analogous
squared-scale recurrence `16 * d (k+1) = 25 * d k` is treated as well.

No Fourier-analysis or PDE conclusion is encoded in these finite arithmetic
statements.
-/

namespace NSMixedHelicity345LatticeRecursion

/-- Iterating the exact `4 -> 5` scale recurrence. -/
theorem iterated_45_identity
    (N : ℕ → ℕ)
    (hrec : ∀ k : ℕ, 4 * N (k + 1) = 5 * N k) :
    ∀ r : ℕ, 4 ^ r * N r = 5 ^ r * N 0 := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        4 ^ (r + 1) * N (r + 1) = 4 ^ r * (4 * N (r + 1)) := by ring
        _ = 4 ^ r * (5 * N r) := by rw [hrec r]
        _ = 5 * (4 ^ r * N r) := by ring
        _ = 5 * (5 ^ r * N 0) := by rw [ih]
        _ = 5 ^ (r + 1) * N 0 := by ring

/-- Every exact depth-`r` chain requires `4^r` divisibility at the initial
lattice scale. -/
theorem finite_45_chain_forces_divisibility
    (N : ℕ → ℕ)
    (hrec : ∀ k : ℕ, 4 * N (k + 1) = 5 * N k)
    (r : ℕ) :
    4 ^ r ∣ N 0 := by
  have hid := iterated_45_identity N hrec r
  have hdiv : 4 ^ r ∣ N 0 * 5 ^ r := by
    refine ⟨N r, ?_⟩
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hid.symm
  have hcop : Nat.Coprime (4 ^ r) (5 ^ r) :=
    (by norm_num : Nat.Coprime 4 5).pow r r
  exact hcop.dvd_of_dvd_mul_right hdiv

/-- There is no nonzero infinite natural-number solution to the exact
self-similar `4 -> 5` scale recurrence. -/
theorem infinite_45_chain_is_zero
    (N : ℕ → ℕ)
    (hrec : ∀ k : ℕ, 4 * N (k + 1) = 5 * N k) :
    N 0 = 0 := by
  by_contra hN0
  have hpos : 0 < N 0 := Nat.pos_of_ne_zero hN0
  let r : ℕ := N 0 + 1
  have hdiv : 4 ^ r ∣ N 0 := finite_45_chain_forces_divisibility N hrec r
  have hle : 4 ^ r ≤ N 0 := Nat.le_of_dvd hpos hdiv
  have hpow : r < 4 ^ r := Nat.lt_pow_self (by norm_num : 1 < 4)
  have hlt : N 0 < 4 ^ r := by
    exact lt_trans (Nat.lt_succ_self (N 0)) hpow
  exact (not_lt_of_ge hle) hlt

/-- Once the initial scale is zero, the recurrence forces the entire chain to
be zero. -/
theorem infinite_45_chain_all_zero
    (N : ℕ → ℕ)
    (hrec : ∀ k : ℕ, 4 * N (k + 1) = 5 * N k) :
    ∀ k : ℕ, N k = 0 := by
  intro k
  induction k with
  | zero => exact infinite_45_chain_is_zero N hrec
  | succ k ih =>
      have hk := hrec k
      rw [ih] at hk
      omega

/-- Iterating the rotation-invariant squared-scale recurrence. -/
theorem iterated_1625_identity
    (d : ℕ → ℕ)
    (hrec : ∀ k : ℕ, 16 * d (k + 1) = 25 * d k) :
    ∀ r : ℕ, 16 ^ r * d r = 25 ^ r * d 0 := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        16 ^ (r + 1) * d (r + 1) = 16 ^ r * (16 * d (r + 1)) := by ring
        _ = 16 ^ r * (25 * d r) := by rw [hrec r]
        _ = 25 * (16 ^ r * d r) := by ring
        _ = 25 * (25 ^ r * d 0) := by rw [ih]
        _ = 25 ^ (r + 1) * d 0 := by ring

/-- A depth-`r` exact squared-scale chain forces `16^r ∣ d 0`. -/
theorem finite_1625_chain_forces_divisibility
    (d : ℕ → ℕ)
    (hrec : ∀ k : ℕ, 16 * d (k + 1) = 25 * d k)
    (r : ℕ) :
    16 ^ r ∣ d 0 := by
  have hid := iterated_1625_identity d hrec r
  have hdiv : 16 ^ r ∣ d 0 * 25 ^ r := by
    refine ⟨d r, ?_⟩
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hid.symm
  have hcop : Nat.Coprime (16 ^ r) (25 ^ r) :=
    (by norm_num : Nat.Coprime 16 25).pow r r
  exact hcop.dvd_of_dvd_mul_right hdiv

/-- The only infinite natural-number solution to the exact squared-scale
recurrence is the zero chain at its initial scale. -/
theorem infinite_1625_chain_is_zero
    (d : ℕ → ℕ)
    (hrec : ∀ k : ℕ, 16 * d (k + 1) = 25 * d k) :
    d 0 = 0 := by
  by_contra hd0
  have hpos : 0 < d 0 := Nat.pos_of_ne_zero hd0
  let r : ℕ := d 0 + 1
  have hdiv : 16 ^ r ∣ d 0 := finite_1625_chain_forces_divisibility d hrec r
  have hle : 16 ^ r ≤ d 0 := Nat.le_of_dvd hpos hdiv
  have hpow : r < 16 ^ r := Nat.lt_pow_self (by norm_num : 1 < 16)
  have hlt : d 0 < 16 ^ r := by
    exact lt_trans (Nat.lt_succ_self (d 0)) hpow
  exact (not_lt_of_ge hle) hlt

#print axioms iterated_45_identity
#print axioms finite_45_chain_forces_divisibility
#print axioms infinite_45_chain_is_zero
#print axioms infinite_45_chain_all_zero
#print axioms iterated_1625_identity
#print axioms finite_1625_chain_forces_divisibility
#print axioms infinite_1625_chain_is_zero

end NSMixedHelicity345LatticeRecursion
