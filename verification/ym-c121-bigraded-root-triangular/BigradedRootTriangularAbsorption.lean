import Mathlib

/-!
# Bi-graded zero/one/two-root triangular absorption

Finite real-algebra firewall for the fixed-root bookkeeping behind a rooted
connected expansion.  The nonroot branch factor is shared across the zero-,
one-, and two-root levels.  Root-placement terms form a finite triangular
hierarchy and change only explicit prefactors and powers of the same positive
denominator `1 - branch`.

This file does not formalize Kirk's rooted Banach spaces, replica--BKAR,
renormalization group maps, multiscale forests, Yang--Mills theory, a mass gap,
or a Clay theorem.
-/

namespace Millennium.YangMills.BigradedRootTriangularAbsorption

/-- Absorb one strict scalar branch recursion. -/
theorem absorb_strict_branch
    (root branch total : ℝ)
    (hbranch : branch < 1)
    (hrec : total ≤ root + branch * total) :
    total ≤ root / (1 - branch) := by
  have hden : 0 < 1 - branch := sub_pos.mpr hbranch
  apply (le_div_iff₀ hden).2
  nlinarith

/--
A zero/one/two-root hierarchy with one common strict nonroot branch factor.
The coefficients `c10`, `c20`, and `c21` encode the finite ways in which a
new passive root may hit a previously controlled lower-root row.

The conclusion displays the exact triangular majorants.  In particular, no
new smallness condition beyond `branch < 1` is introduced at one or two roots.
-/
theorem zero_one_two_root_triangular_absorption
    (root0 root1 root2 branch c10 c20 c21 total0 total1 total2 : ℝ)
    (hbranch : branch < 1)
    (hc10 : 0 ≤ c10)
    (hc20 : 0 ≤ c20)
    (hc21 : 0 ≤ c21)
    (h0 : total0 ≤ root0 + branch * total0)
    (h1 : total1 ≤ root1 + branch * total1 + c10 * total0)
    (h2 : total2 ≤ root2 + branch * total2 + c21 * total1 + c20 * total0) :
    total0 ≤ root0 / (1 - branch) ∧
      total1 ≤
        (root1 + c10 * (root0 / (1 - branch))) / (1 - branch) ∧
      total2 ≤
        (root2 +
            c21 *
              ((root1 + c10 * (root0 / (1 - branch))) / (1 - branch)) +
            c20 * (root0 / (1 - branch))) /
          (1 - branch) := by
  have h0bound : total0 ≤ root0 / (1 - branch) :=
    absorb_strict_branch root0 branch total0 hbranch h0
  have hc10bound :
      c10 * total0 ≤ c10 * (root0 / (1 - branch)) :=
    mul_le_mul_of_nonneg_left h0bound hc10
  have hrec1 :
      total1 ≤
        (root1 + c10 * (root0 / (1 - branch))) + branch * total1 := by
    calc
      total1 ≤ root1 + branch * total1 + c10 * total0 := h1
      _ ≤ root1 + branch * total1 + c10 * (root0 / (1 - branch)) :=
        add_le_add_left hc10bound (root1 + branch * total1)
      _ = (root1 + c10 * (root0 / (1 - branch))) + branch * total1 := by
        ring
  have h1bound :
      total1 ≤
        (root1 + c10 * (root0 / (1 - branch))) / (1 - branch) :=
    absorb_strict_branch
      (root1 + c10 * (root0 / (1 - branch)))
      branch total1 hbranch hrec1
  have hc21bound :
      c21 * total1 ≤
        c21 *
          ((root1 + c10 * (root0 / (1 - branch))) / (1 - branch)) :=
    mul_le_mul_of_nonneg_left h1bound hc21
  have hc20bound :
      c20 * total0 ≤ c20 * (root0 / (1 - branch)) :=
    mul_le_mul_of_nonneg_left h0bound hc20
  have hrec2 :
      total2 ≤
        (root2 +
            c21 *
              ((root1 + c10 * (root0 / (1 - branch))) / (1 - branch)) +
            c20 * (root0 / (1 - branch))) +
          branch * total2 := by
    calc
      total2 ≤
          root2 + branch * total2 + c21 * total1 + c20 * total0 := h2
      _ ≤
          root2 + branch * total2 +
              c21 *
                ((root1 + c10 * (root0 / (1 - branch))) /
                  (1 - branch)) +
            c20 * (root0 / (1 - branch)) :=
        add_le_add
          (add_le_add_left hc21bound (root2 + branch * total2))
          hc20bound
      _ =
          (root2 +
              c21 *
                ((root1 + c10 * (root0 / (1 - branch))) /
                  (1 - branch)) +
              c20 * (root0 / (1 - branch))) +
            branch * total2 := by
        ring
  have h2bound :
      total2 ≤
        (root2 +
            c21 *
              ((root1 + c10 * (root0 / (1 - branch))) / (1 - branch)) +
            c20 * (root0 / (1 - branch))) /
          (1 - branch) :=
    absorb_strict_branch
      (root2 +
        c21 *
          ((root1 + c10 * (root0 / (1 - branch))) / (1 - branch)) +
        c20 * (root0 / (1 - branch)))
      branch total2 hbranch hrec2
  exact ⟨h0bound, h1bound, h2bound⟩

#print axioms absorb_strict_branch
#print axioms zero_one_two_root_triangular_absorption

end Millennium.YangMills.BigradedRootTriangularAbsorption
