import Mathlib

/-!
# Faizal--Shabir irrelevant-source / invariant-graph firewall

Finite scalar algebra for the C189 audit of the weak-coupling RG in
arXiv:2606.19362v1.

The manuscript's earlier weak RG estimate contains an additive `g^2` source
in the irrelevant coordinate, while the later Theorem 10.7 recurrence drops
that source and treats `K = 0` as invariant.  These finite lemmas record why
that distinction is load-bearing for the beta function: an allowed
`K = O(g^2)` contribution makes the displayed mixed term `g*K` cubic, not
fifth order.

This file does not formalize the Faizal--Shabir Banach RG map, an invariant
manifold, Yang--Mills theory, OS reconstruction, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirIrrelevantSourceInvariantGraphFirewall

/-- A recurrence with a nonnegative additive `c*g^2` source is compatible,
already in one step, with an irrelevant coordinate of exact order `g^2`. -/
theorem g2_source_recurrence_allows_order_g2
    (g q c K : ℝ)
    (hq : 0 ≤ q)
    (hK : 0 ≤ K) :
    c * g ^ 2 ≤ q * K + c * g ^ 2 := by
  have hqK : 0 ≤ q * K := mul_nonneg hq hK
  linarith

/-- If an irrelevant coordinate is of order `c*g^2`, then the mixed beta
remainder `g*K` is exactly cubic. -/
theorem order_g2_activity_makes_mixed_term_cubic
    (g c : ℝ) :
    g * (c * g ^ 2) = c * g ^ 3 := by
  ring

/-- Exact ratio identity: for nonzero `g`, a cubic term exceeds a fifth-order
scale by the factor `1/g^2`. -/
theorem cubic_to_fifth_ratio
    (g c : ℝ)
    (hg : g ≠ 0) :
    (c * g ^ 3) / g ^ 5 = c / g ^ 2 := by
  field_simp
  ring

/-- In particular, for `0 < g < 1` and positive coefficient, the cubic mixed
term is strictly larger than the same-coefficient fifth-order term. -/
theorem cubic_strictly_dominates_fifth_near_zero
    (g c : ℝ)
    (hg0 : 0 < g)
    (hg1 : g < 1)
    (hc : 0 < c) :
    c * g ^ 5 < c * g ^ 3 := by
  have hg2 : g ^ 2 < 1 := by nlinarith [sq_nonneg g]
  have hg3 : 0 < g ^ 3 := pow_pos hg0 3
  have hmul : g ^ 3 * g ^ 2 < g ^ 3 * 1 :=
    mul_lt_mul_of_pos_left hg2 hg3
  have hcpos : 0 < c := hc
  have := mul_lt_mul_of_pos_left hmul hcpos
  simpa [pow_succ, pow_two] using this

/-- If the additive source actually realizes `K = c*g^2`, a subsequent
`g*K` term changes the cubic coefficient by `c`. -/
theorem cubic_coefficient_shift_from_g2_graph
    (g beta c : ℝ) :
    (g - beta * g ^ 3) + g * (c * g ^ 2) =
      g - (beta - c) * g ^ 3 := by
  ring

#print axioms g2_source_recurrence_allows_order_g2
#print axioms order_g2_activity_makes_mixed_term_cubic
#print axioms cubic_to_fifth_ratio
#print axioms cubic_strictly_dominates_fifth_near_zero
#print axioms cubic_coefficient_shift_from_g2_graph

end Millennium.YangMills.FaizalShabirIrrelevantSourceInvariantGraphFirewall
