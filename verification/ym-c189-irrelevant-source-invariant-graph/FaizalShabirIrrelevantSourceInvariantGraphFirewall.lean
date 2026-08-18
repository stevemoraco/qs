import Mathlib

/-!
# Faizal--Shabir irrelevant-source / invariant-graph firewall

Finite scalar algebra for the C189 audit of the weak-coupling RG in
arXiv:2606.19362v1.

The manuscript's earlier weak RG estimate contains an additive `g^2` source
in the irrelevant coordinate, while the later Theorem 10.7 recurrence drops
that source and treats `K = 0` as invariant. These finite lemmas record why
that distinction is load-bearing for the beta function: an allowed
`K = O(g^2)` contribution makes the displayed mixed term `g*K` cubic, not
fifth order.

The final declarations also record the leading coefficient forced by a scalar
invariant-graph equation `A = q*A + s`: namely `A = s/(1-q)`. Thus a mixed
marginal term `ell*g*K_*(g)` generically shifts the cubic coefficient by
`ell*s/(1-q)` unless a separate normalization/cancellation theorem removes or
incorporates that shift.

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
  field_simp [hg]

/-- In particular, for `0 < g < 1` and positive coefficient, the cubic mixed
term is strictly larger than the same-coefficient fifth-order term. -/
theorem cubic_strictly_dominates_fifth_near_zero
    (g c : ℝ)
    (hg0 : 0 < g)
    (hg1 : g < 1)
    (hc : 0 < c) :
    c * g ^ 5 < c * g ^ 3 := by
  have hg2 : g ^ 2 < 1 := by nlinarith [sq_nonneg g]
  have hcg3 : 0 < c * g ^ 3 := mul_pos hc (pow_pos hg0 3)
  calc
    c * g ^ 5 = (c * g ^ 3) * g ^ 2 := by ring
    _ < (c * g ^ 3) * 1 := mul_lt_mul_of_pos_left hg2 hcg3
    _ = c * g ^ 3 := by ring

/-- If the additive source actually realizes `K = c*g^2`, a subsequent
`g*K` term changes the cubic coefficient by `c`. -/
theorem cubic_coefficient_shift_from_g2_graph
    (g beta c : ℝ) :
    (g - beta * g ^ 3) + g * (c * g ^ 2) =
      g - (beta - c) * g ^ 3 := by
  ring

/-- Leading scalar invariant-graph coefficient. If the quadratic graph
coefficient satisfies `A = q*A + s`, then it is forced to be `s/(1-q)` as
soon as the stable multiplier is not exactly one. -/
theorem invariant_graph_quadratic_coefficient
    (A q s : ℝ)
    (hq : q ≠ 1)
    (hgraph : A = q * A + s) :
    A = s / (1 - q) := by
  have hden : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  apply (eq_div_iff hden).2
  nlinarith [hgraph]

/-- A mixed marginal term `ell*g*K_*(g)` on a quadratic graph with leading
coefficient `s/(1-q)` shifts the cubic coefficient by `ell*s/(1-q)`. -/
theorem invariant_graph_induced_cubic_shift
    (g beta ell q s : ℝ) :
    (g - beta * g ^ 3) + ell * g * ((s / (1 - q)) * g ^ 2) =
      g - (beta - ell * s / (1 - q)) * g ^ 3 := by
  ring

#print axioms g2_source_recurrence_allows_order_g2
#print axioms order_g2_activity_makes_mixed_term_cubic
#print axioms cubic_to_fifth_ratio
#print axioms cubic_strictly_dominates_fifth_near_zero
#print axioms cubic_coefficient_shift_from_g2_graph
#print axioms invariant_graph_quadratic_coefficient
#print axioms invariant_graph_induced_cubic_shift

end Millennium.YangMills.FaizalShabirIrrelevantSourceInvariantGraphFirewall
