import Mathlib

/-!
# Round 214 P versus NP finite cores

This file formalizes only the scalar incidence ledger, the compressed-output
average-degree implication, an abstract kernel-collision identity, and the
scalar endpoint of the finite minimax averaging argument.

It does not formalize binary matrices, multigraphs, the Moore bound, circuits,
complexity classes, the Chen--Li--Yang theorem, or `P != NP`.
-/

namespace Millennium
namespace Round214PNP

/-- Under a total incidence budget `W ≤ 2n+s`, if the columns outside a
positive support split into `r` columns of weight one/two and `h` columns of
weight at least three, then the low-incidence population obeys
`n-s-3L ≤ 2r`.  The variable `q` is the number of weight-one columns. -/
theorem low_incidence_column_budget
    (n L s q r h W : ℝ)
    (hpartition : r + h = n - L)
    (hupper : W ≤ 2 * n + s)
    (hlower : 2 * r - q + 3 * h ≤ W)
    (hq : q ≤ r) :
    n - s - 3 * L ≤ 2 * r := by
  linarith

/-- If the parameter lower bound on `r` beats twice the rooted output-vertex
count, then the rooted low-incidence multigraph has average half-degree
strictly larger than two.  The actual graph-theoretic cycle extraction is not
formalized here. -/
theorem compressed_output_forces_dense_low_incidence_core
    (n L s m r : ℝ)
    (hm : 0 < m + 1)
    (hbudget : n - s - 3 * L ≤ 2 * r)
    (hcompression : 4 * (m + 1) < n - s - 3 * L) :
    2 < r / (m + 1) := by
  rw [lt_div_iff₀ hm]
  linarith

/-- A perturbation in the kernel of an additive hash leaves the hash value
unchanged. -/
theorem kernel_perturbation_same_hash
    {A B : Type*} [AddGroup A] [AddGroup B]
    (H : A →+ B) (P Z : A) (hZ : H Z = 0) :
    H (P + Z) = H P := by
  simp [map_add, hZ]

/-- An arbitrary recognizer on hash outputs cannot distinguish two inputs with
identical hash values. -/
theorem image_recognizer_accepts_collision
    {A B : Type*}
    (H : A → B) (R : B → Bool) (P X : A)
    (hhash : H X = H P) (haccept : R (H P) = true) :
    R (H X) = true := by
  simpa [hhash] using haccept

/-- Scalar endpoint of the universal-pool minimax argument: if total accepted
mass is at least one and at most `N` times the largest point mass, then some
point mass is at least `1/N`. -/
theorem finite_pool_minimax_scalar
    (N total pmax : ℝ)
    (hN : 0 < N)
    (htotal : 1 ≤ total)
    (hcap : total ≤ N * pmax) :
    1 / N ≤ pmax := by
  rw [div_le_iff₀ hN]
  exact htotal.trans hcap

/-- Combining the incidence ledger and compression gate directly. -/
theorem incidence_budget_to_dense_core
    (n L s q r h W m : ℝ)
    (hpartition : r + h = n - L)
    (hupper : W ≤ 2 * n + s)
    (hlower : 2 * r - q + 3 * h ≤ W)
    (hq : q ≤ r)
    (hm : 0 < m + 1)
    (hcompression : 4 * (m + 1) < n - s - 3 * L) :
    2 < r / (m + 1) := by
  apply compressed_output_forces_dense_low_incidence_core n L s m r hm
  · exact low_incidence_column_budget n L s q r h W
      hpartition hupper hlower hq
  · exact hcompression

#print axioms low_incidence_column_budget
#print axioms compressed_output_forces_dense_low_incidence_core
#print axioms kernel_perturbation_same_hash
#print axioms image_recognizer_accepts_collision
#print axioms finite_pool_minimax_scalar
#print axioms incidence_budget_to_dense_core

end Round214PNP
end Millennium
