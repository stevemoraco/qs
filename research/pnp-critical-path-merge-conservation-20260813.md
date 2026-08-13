# P versus NP braid: critical-path merge conservation

Date: 2026-08-13
Status: finite structural refinement plus semantic interface; **not** P versus NP.

## Executive result

The exact critical-path slack identity extends cleanly beyond the pathology-free case. Intersecting critical paths are not arbitrary: because every nonterminal vertex on a critical path has out-degree exactly one, two critical paths that meet must share a suffix and have the same terminal endpoint. Thus path intersection is an equivalence relation on inputs, with equivalence classes equal to the sets of inputs whose critical paths have the same endpoint.

Let

* `n` be the number of inputs;
* `r` be the number of **distinct critical-path endpoints**;
* `m := n-r` be the critical-path merge deficit;
* `o in {0,1}` indicate whether the unique output is Type 1;
* `delta_1,delta_2 >= 0` be the same exact Type-1/Type-2 outgoing-wire excesses as in the banked pathology-free ledger.

For every normalized single-output fan-in-two circuit with **no isolated input**, whether or not critical paths intersect,

\[
\boxed{
|G|-(2n-2)
= -m +(1-o)+\delta_1+\delta_2.
}
\]

Equivalently,

\[
\boxed{
|G|=2n-2-(n-r)+(1-o)+\delta_1+\delta_2.
}
\]

The old identity is exactly the special case `r=n`, i.e. `m=0`.

This matters semantically when combined with `L_n^diamond` from `pnp-orientation-marker-firewall-20260813.md`. A perfect-completeness circuit for that language which rejects both global markers `0^n,1^n` accepts the distinct false positive

\[
1^n-e_u-e_v
\]

for every intersecting pair of critical paths `{u,v}`. If the endpoint classes have sizes `k_1,...,k_r`, the number of such canonical errors is

\[
E=\sum_i\binom{k_i}{2}.
\]

Since `binom(k,2) >= k-1` for `k>=1`,

\[
\boxed{E\ge\sum_i(k_i-1)=n-r=m.}
\]

So every merge credit that lowers the `2n-2` structural baseline buys at least one **distinct semantic false positive with congestion one**, unless the circuit has already hit one of the two global markers.

The unresolved low-surplus problem is thereby sharpened again: critical-path merges are already semantically paid. What remains is to extract/charge witnesses for the nonnegative defect mass `(1-o)+delta_1+delta_2`, especially in the `m=0` pathology-free regime.

## 1. Why intersection classes are endpoint classes

A critical path is a sequence

\[
v_0,v_1,\ldots,v_k
\]

starting at an input, such that every `v_i` for `i<k` has out-degree exactly one and the terminal `v_k` has out-degree different from one.

Suppose two critical paths share a vertex `z`.

* `z` cannot be terminal on one path and nonterminal on the other: the same circuit vertex cannot simultaneously have out-degree `!=1` and out-degree `1`.
* If `z` is nonterminal on both paths, its unique outgoing edge forces both paths to take the same next vertex. Repeating, they share the entire suffix from `z` onward.
* Therefore their terminal vertices are equal.

Conversely, if two critical paths have the same terminal vertex, they intersect there. Hence

\[
\boxed{
P_u\cap P_v\ne\varnothing
\iff
\operatorname{end}(P_u)=\operatorname{end}(P_v).
}
\]

The critical-path intersection graph is therefore a disjoint union of cliques, one clique for each distinct endpoint. This observation is model-independent once the critical-path definition is fixed.

## 2. Generalized Type-1 / Type-2 wire ledger

Let Type 1 be the union of all critical-path vertices and Type 2 its complement. Write

* `c1` = number of Type-1 nodes;
* `c2` = number of Type-2 nodes;
* `l` = number of Type-1 to Type-1 wires;
* `W12,W21,W22` for the other wire classes.

All `n` inputs are Type 1, so the number of Type-1 gates is `c1-n`.

There are now `r`, rather than `n`, distinct Type-1 terminal vertices. Every other Type-1 vertex has out-degree exactly one. Because isolated inputs are excluded and the circuit is normalized, every non-output terminal has out-degree at least two. Hence the minimum total Type-1 outgoing-wire count is

\[
(c_1-r)+2(r-o)=c_1+r-2o.
\]

Define the exact nonnegative excess

\[
\delta_1
:=W_{12}-(c_1+r-2o-l)\ge0,
\]

so

\[
W_{12}=c_1+r-2o-l+\delta_1.
\]

Every Type-1 gate has fan-in two, giving

\[
W_{21}=2(c_1-n)-l.
\]

As before, every non-output Type-2 gate has positive out-degree. Define

\[
\delta_2
:=(W_{21}+W_{22})-(c_2-(1-o))\ge0.
\]

Then

\[
W_{22}=c_2-1+o+\delta_2-2(c_1-n)+l.
\]

Every Type-2 node is a fan-in-two gate, so

\[
2c_2=W_{12}+W_{22}.
\]

Substituting gives

\[
2c_2
=-c_1+c_2+r+2n-1-o+\delta_1+\delta_2,
\]

hence

\[
c_1+c_2=r+2n-1-o+\delta_1+\delta_2.
\]

Subtract the `n` input nodes to obtain the gate count:

\[
|G|
=n+r-1-o+\delta_1+\delta_2.
\]

Writing `m=n-r` yields

\[
\boxed{
|G|=2n-2-m+(1-o)+\delta_1+\delta_2.
}
\]

No asymptotic estimate or discarded nonnegative term is used.

## 3. Merge credits are already semantic witnesses

Let the endpoint equivalence classes have sizes `k_1,...,k_r`, so

\[
\sum_i k_i=n,
\qquad
m=n-r=\sum_i(k_i-1).
\]

The number of intersecting unordered path pairs is

\[
E=\sum_i\binom{k_i}{2}.
\]

For every integer `k>=1`,

\[
\binom{k}{2}-(k-1)
=\frac{(k-1)(k-2)}2\ge0.
\]

Therefore `E>=m`.

Now use the orientation-marker language

\[
L_n^\diamond=\{x:|x|\in\{1,2,n-1\}\}.
\]

The companion finite semantic theorem says that if a perfect-completeness circuit rejects both `0^n` and `1^n`, then every intersecting pair `{u,v}` forces

\[
C(1^n-e_u-e_v)=1.
\]

Different pairs give different bit strings. Hence the circuit has at least `E>=m` distinct false positives on the weight-`n-2` layer.

This is an exact structural-to-semantic exchange rate:

\[
\boxed{
\text{one critical-path merge deficit unit}
\Longrightarrow
\text{at least one distinct canonical error},
}
\]

unless a two-point global hard core has already caught the circuit.

## 4. Frontier form

Let

\[
D=(1-o)+\delta_1+\delta_2.
\]

The generalized identity is

\[
|G|-(2n-2)=D-m.
\]

Thus at the magnification frontier `|G|<=2n+S`,

\[
\boxed{D-m\le S+2},
\]

or equivalently

\[
D\le m+S+2.
\]

The `m` units are not mysterious anymore: for circuits avoiding the two common markers they come with at least `m` distinct pair-complement errors. The genuinely unpaid part is the defect structure that survives after merges are accounted for.

A useful hostile interpretation is:

* if `m` is large, semantic witness count is already large;
* if `m` is small, the critical paths are nearly disjoint and the circuit is close to the exact pathology-free ledger where only `S+2+o(m)` defect units remain;
* if `m=0`, this reduces exactly to the previously banked `D<=S+2` target.

This is a cleaner bridge to the requested `O(log log n)` congestion program than treating all intersecting circuits as one undifferentiated pathology.

## 5. Claimant / critic / rebuilder

### Claimant

Use the two common markers first. For surviving circuits, debit every endpoint merge unit against a unique weight-`n-2` false positive. Then prove the remaining semantic errors by charging only the defect units `D` in the nearly-disjoint critical-path forest.

### Critic

The identity alone does not force `m` to be large, nor does it force any error in a completely disjoint (`m=0`) circuit. Also, `D` can grow with `m`; the equation only controls the net quantity `D-m`. Nothing yet proves that a defect unit supports only `O(log log n)` semantic repairs.

### Rebuilder

The next finite structural target should be formulated on a **critical-path forest with endpoint classes already contracted**. Remove the merge-generated pair witnesses from the bookkeeping and ask how many background-orientation reversals or low/high rank switches can be realized per unit of `delta_1+delta_2+(1-o)` in that quotient structure.

This avoids spending future work re-proving witnesses for merges that are now canonical.

## 6. Lean scope

The scalar shadow of the new wire identity is added to

`verification/pnp-critical-path-slack/PNPCriticalPathSlackFinite.lean`.

The graph-theoretic facts that critical-path intersections are endpoint equivalence classes and that `E>=m` are not yet kernel-formalized there; the Lean theorem takes the generalized wire equation as an explicit hypothesis and proves the resulting gate/slack identities by linear arithmetic.

## 7. Barrier and model audit

* **Model:** unrestricted fan-in-two `B_2`; only graph degrees and fan-in-two wire counts enter the conservation law.
* **Class preservation:** no hidden/nonuniform language selection is used. The semantic interface uses the explicit polynomially sparse `P` language `L_n^diamond`.
* **Relativization:** the structural identity and marker theorem are finite and relativizing; no relativization escape is claimed.
* **Natural proofs:** no large constructive truth-table property is produced.
* **Algebrization:** no arithmetization is used.
* **Finite to asymptotic:** the identity is exact for each finite circuit. The only asymptotic substitution is the explicit inequality `|G|<=2n+S`.

## 8. Provenance

Critical-path definitions and the original disjoint-path wire count come from:

* Zhiyuan Fan, Jiatu Li, Tianqi Yang, ECCC TR21-125 rev. 1, especially the general-circuit critical-path lower bound;
* Lijie Chen, Jiatu Li, Tianqi Yang, CCC 2022 / ECCC TR22-086 rev. 1, Definition 4.6 and Lemmas 4.7--4.8.

The merge-class extension, exact generalized conservation identity, and its combination with the orientation-marker semantic theorem are new to this repository as of 2026-08-13.

FIVE-ALARM: OFF.
