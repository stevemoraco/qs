import Mathlib

/-!
# Finite Lean firewall for two fatal type errors in a claimed Hodge proof

This file formalizes only the load-bearing set-theoretic and correspondence-
grade arithmetic.  It does not formalize secant varieties, Chow groups,
Hodge structures, or the Hodge conjecture.
-/

namespace HodgeClaimAudit

/-- If a variety `A` is contained in a proposed secant locus `Sec`, then the
set-theoretic intersection of that locus with `A` is exactly `A`. -/
theorem intersection_eq_of_subset {ι : Type*} {A Sec : Set ι}
    (hA : A ⊆ Sec) :
    Sec ∩ A = A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨hA hx, hx⟩

/-- Abstract codimension firewall: an intersection with a subobject already
contained in the other factor cannot simultaneously be that same subobject
and have positive codimension in it. -/
theorem contained_intersection_not_positive_codimension
    {ι : Type*} {A Sec : Set ι}
    (hA : A ⊆ Sec)
    (codim : Set ι → Set ι → ℕ)
    (hself : codim A A = 0)
    {n : ℕ} (hn : 0 < n)
    (hclaim : codim A (Sec ∩ A) = n) : False := by
  have hinter : Sec ∩ A = A := intersection_eq_of_subset hA
  rw [hinter, hself] at hclaim
  omega

/-- Codimension of a composition of self-correspondences on an `n`-fold.
The standard formula is `r + s - n`.  Integers are used so the bookkeeping
itself does not hide truncated subtraction. -/
def composeCodim (n r s : ℤ) : ℤ := r + s - n

/-- Codimension obtained by iterating a codimension-`r` correspondence,
starting with the diagonal (the zero-fold composition) in codimension `n`. -/
def iterCodim (n r : ℤ) : ℕ → ℤ
  | 0 => n
  | m + 1 => composeCodim n (iterCodim n r m) r

/-- A Lefschetz raising correspondence has codimension `n+1`; its `m`-fold
composition has codimension `n+m`, not codimension `m`. -/
theorem raising_power_codim (n : ℤ) : ∀ m : ℕ,
    iterCodim n (n + 1) m = n + (m : ℤ) := by
  intro m
  induction m with
  | zero => simp [iterCodim]
  | succ m ih =>
      simp [iterCodim, composeCodim, ih]
      ring

/-- Transposition does not change the codimension of an algebraic cycle. -/
def transposeCodim (r : ℤ) : ℤ := r

/-- Therefore transposing a power of the raising correspondence leaves its
codimension equal to `n+m`. -/
theorem transpose_raising_power_codim (n : ℤ) (m : ℕ) :
    transposeCodim (iterCodim n (n + 1) m) = n + (m : ℤ) := by
  simp [transposeCodim, raising_power_codim]

/-- A codimension-`r` self-correspondence on an `n`-fold shifts cohomological
degree by `2(r-n)`. -/
def cohomologicalShift (n r : ℤ) : ℤ := 2 * (r - n)

/-- Any correspondence realizing the inverse
`H^(2n-k) → H^k` must have codimension exactly `k`. -/
theorem inverse_lefschetz_required_codim {n k r : ℤ}
    (hshift : cohomologicalShift n r = k - (2 * n - k)) :
    r = k := by
  simp [cohomologicalShift] at hshift
  linarith

/-- For a nontrivial Lefschetz string (`k<n`), the transpose of the
`(n-k)`-fold raising operator has codimension `2n-k`, which is not `k`. -/
theorem transpose_power_wrong_codim {n k : ℤ} (hkn : k < n) :
    2 * n - k ≠ k := by
  linarith

/-- The same object has positive degree shift `+2(n-k)`, whereas the inverse
Hard Lefschetz map requires the negative shift `-2(n-k)`. -/
theorem transpose_power_wrong_direction {n k : ℤ} (hkn : k < n) :
    cohomologicalShift n (2 * n - k) = 2 * (n - k) ∧
    cohomologicalShift n k = -2 * (n - k) ∧
    cohomologicalShift n (2 * n - k) ≠ cohomologicalShift n k := by
  constructor
  · simp [cohomologicalShift]
    ring
  constructor
  · simp [cohomologicalShift]
    ring
  · simp [cohomologicalShift]
    linarith

/-- Smallest numerical test: on a curve, composing two codimension-two
raising correspondences has codimension three. -/
theorem p1_double_raise_codim : composeCodim 1 2 2 = 3 := by
  norm_num [composeCodim]

/-- On a curve, the inverse `H^2 → H^0` requires codimension zero, while the
transposed raising correspondence still has codimension two. -/
theorem p1_inverse_type_mismatch : (2 : ℤ) ≠ 0 := by
  norm_num

#print axioms intersection_eq_of_subset
#print axioms contained_intersection_not_positive_codimension
#print axioms raising_power_codim
#print axioms transpose_raising_power_codim
#print axioms inverse_lefschetz_required_codim
#print axioms transpose_power_wrong_codim
#print axioms transpose_power_wrong_direction
#print axioms p1_double_raise_codim
#print axioms p1_inverse_type_mismatch

end HodgeClaimAudit
