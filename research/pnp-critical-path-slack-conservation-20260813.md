# P vs NP braid: exact critical-path slack conservation

Date: 2026-08-13
Branch: `agent/gpt56-pnp-indexed-router-firewall-20260813-run2`
Status: finite structural theorem and source audit; **not** a P-vs-NP proof.

## Executive result

Re-running the Fan--Li--Yang critical-path wire count without discarding its nonnegative error terms yields an **exact conservation law for every normalized single-output pathology-free `B_2` circuit**:

\[
\boxed{
|G|-(2n-2)=(1-o)+\delta_1+\delta_2.
}
\]

Here `o in {0,1}` records whether the unique output node lies on a critical path, and `delta_1,delta_2` are exact nonnegative excess-wire terms for Type-1 and Type-2 nodes. Therefore a pathology-free circuit with at most `2n+S` gates has

\[
\boxed{(1-o)+\delta_1+\delta_2\le S+2.}
\]

This is the cleanest exact **slack currency** found so far at the magnification frontier. It does not yet manufacture semantic errors, but it converts the vague goal “charge witnesses to surplus gates” into a precise finite target: in the no-intersection/no-isolated regime, every semantic repair beyond the `2n-2` skeleton must be charged to one of only `S+2` structural defect units.

A second source audit matters for exact accounting. The published CCC 2022 Chen--Li--Yang proof states Lemma 4.7 as the lower bound `>=2n-2`, then immediately says it suffices for the claimed `(2n-2)` obstruction to handle only intersecting critical paths or isolated inputs. That implication does not cover pathology-free circuits of **exactly** `2n-2` gates. Equality is not vacuous: a normalized pathology-free topology with exactly `2n-2` gates exists for every `n>=2`. Thus the inclusive `2n-2` obstruction step should be quarantined until an equality-case semantic lemma or a convention resolving the boundary is supplied. This does **not** show Corollary 4.9 false; it isolates a missing equality case in the displayed proof.

---

## 1. Definitions

Let `C` be a normalized `n`-input, single-output, fan-in-two `B_2` circuit. Assume:

1. no two critical paths intersect;
2. no input variable has out-degree zero.

Following Fan--Li--Yang, partition all circuit nodes into:

- **Type 1:** nodes lying on some critical path;
- **Type 2:** all remaining nodes.

Let:

- `c1` = number of Type-1 nodes;
- `c2` = number of Type-2 nodes;
- `l` = number of Type-1 -> Type-1 wires;
- `o` = number of output nodes of Type 1. Since the circuit has one output, `o in {0,1}`.

Because the critical paths are disjoint, there are exactly `n` Type-1 path endpoints, so exactly `c1-n` Type-1 nodes have out-degree one. Normalization and absence of isolated variables imply the lower-bound wire counts used by Fan--Li--Yang.

Instead of dropping the excess, define it exactly.

Let `W12` be the number of Type-1 -> Type-2 wires and define

\[
\delta_1
:=W_{12}-\bigl(c_1+n-2o-l\bigr)\ge0.
\]

Equivalently, `delta_1` is the Type-1 outgoing-wire excess above the FLY minimum after removing the `l` internal Type-1 wires.

Let `W21` and `W22` be the Type-2 -> Type-1 and Type-2 -> Type-2 wire counts. Every Type-1 gate has fan-in exactly two, so

\[
W_{21}=2(c_1-n)-l.
\]

Every non-output Type-2 gate has out-degree at least one. Since there are `1-o` output nodes in Type 2, define the exact nonnegative Type-2 outgoing excess

\[
\delta_2
:= (W_{21}+W_{22})-\bigl(c_2-(1-o)\bigr)\ge0.
\]

---

## 2. Exact conservation theorem

From the definitions,

\[
W_{12}=c_1+n-2o-l+\delta_1.
\]

Also

\[
W_{22}
=c_2-(1-o)+\delta_2-W_{21}
=c_2-1+o+\delta_2-2(c_1-n)+l.
\]

Every Type-2 node is a gate of fan-in two, so its total incoming wire count is exactly `2c2`:

\[
2c_2=W_{12}+W_{22}.
\]

Substitution gives

\[
2c_2
=-c_1+c_2+3n-1-o+\delta_1+\delta_2,
\]

hence

\[
c_1+c_2=3n-1-o+\delta_1+\delta_2.
\]

The total gate count is total nodes minus the `n` input nodes, therefore

\[
\boxed{
|G|=2n-1-o+\delta_1+\delta_2
=2n-2+(1-o)+\delta_1+\delta_2.
}
\]

All terms on the right of the baseline are nonnegative integers.

### Frontier corollary

If `|G| <= 2n+S`, then

\[
\boxed{
(1-o)+\delta_1+\delta_2\le S+2.
}
\]

If `|G|=2n-2`, then necessarily

\[
o=1,\qquad \delta_1=\delta_2=0.
\]

Thus equality forces every inequality in the FLY wire count to be tight.

This is stronger information than Lemma 7.4's lower bound and is exactly the kind of quantitative stability invariant needed for a semantic witness charging theorem.

---

## 3. Equality is structurally attainable

The equality case cannot be discarded as impossible topology.

For every `n>=2`, construct `2n-2` gates `g_1,...,g_{2n-2}` in a chain. Feed `x_n` into `g_1`, and feed `g_t` into `g_{t+1}`. The second input of each gate is chosen from `x_1,...,x_{n-1}` so that each of those `n-1` variables occurs in exactly two second-input slots. Mark `g_{2n-2}` as the output.

Then:

- `x_n` has out-degree one and its critical path is `x_n,g_1,...,g_{2n-2}`;
- each `x_i`, `i<n`, has out-degree two and therefore its critical path is the singleton `{x_i}`;
- these `n` critical paths are pairwise disjoint;
- no input is isolated;
- the only out-degree-zero gate is the output, so the circuit is normalized;
- there are exactly `2n-2` gates.

Gate truth tables are irrelevant to this topological statement.

So a proof that every circuit of size **at most** `2n-2` has an intersection or isolated input cannot follow from Lemma 4.7 alone.

---

## 4. Chen--Li--Yang equality-boundary audit

The published CCC 2022 version says:

- Lemma 4.7: a normalized single-output circuit with no intersecting critical paths and no input of out-degree zero has **at least** `2n-2` gates;
- then defines the obstruction labels on weights `0,2,n-2,n-1` as zero and weights `1,n` as one;
- then says, “According to Lemma 4.7, we only need to prove” that circuits with an intersection or isolated input disagree with the obstruction;
- Corollary 4.9 then states an explicit obstruction against `2n-2` size `B_2` circuits;
- Corollary 4.11 states the corresponding probabilistic sparse-language lower bound at size `2n-2`.

The ECCC revision has the same step, and the CCC proceedings version preserves it verbatim.

Under the usual inclusive interpretation “circuits of size at most `2n-2`”, Lemma 4.7 only forces a pathology **strictly below** `2n-2`; it leaves the equality class untreated. The explicit chain topology above proves that this equality class is nonempty even after normalization and the no-isolated/no-intersection conditions.

Therefore the displayed proof establishes the obstruction immediately for size at most `2n-3` (integer gate count), while the inclusive `2n-2` boundary requires one additional semantic argument about tight circuits.

I am **not** asserting that Corollary 4.9 is false. Possibilities still open include:

1. a separate equality-case semantic fact makes every tight pathology-free circuit disagree with the listed labels;
2. a size convention intended by the authors excludes the boundary, though the surrounding `SIZE` usage should be checked before relying on that;
3. the published proof has a one-gate omission.

For this project, the safe policy is to quarantine the inclusive boundary and never spend or charge the `2n-2` baseline gate as if the equality case were already classified.

### Relation to Fan--Li--Yang

The original FLY Lemma 7.4 proves the same `>=2n-2m` lower bound by wire counting. Its Theorem 7.6 proof also contains boundary-sensitive prose: it first supposes realization by `2n-2m` gates and says Lemma 7.4 forces a pathology, while later the same proof refers to circuit complexity *smaller than* `2n-2m`. The stated lower bound “requires at least `2n-2m` gates” itself only needs exclusion below the threshold, so this does not by itself invalidate that lower-bound statement. It reinforces that equality should not be silently imported from the counting lemma.

---

## 5. Why the conservation law is high leverage for the current target

The CLY semantic lemma already handles one structural pathology: if two critical paths intersect, agreement with their sparse obstruction forces a two-variable restriction to look XOR-like near the all-zero assignment and AND-like near the all-one assignment, which is impossible through the same first intersection gate. Under perfect completeness, any disagreement cannot occur on the required positive labels, so it becomes a false positive on one of the sparse negative labels.

An isolated input is even simpler under perfect completeness on all weight-one inputs: independence of `x_i` makes `C(0^n)=C(e_i)=1`, so `0^n` is a false positive.

Therefore every perfect-completeness circuit falls into:

1. isolated input -> immediate sparse negative witness;
2. intersecting critical paths -> CLY sparse negative witness;
3. no pathologies -> exact defect budget `(1-o)+delta_1+delta_2 <= S+2`.

This gives a much sharper next theorem than the visible-block route:

\[
\boxed{
\text{For pathology-free perfect-completeness circuits, charge a large}\
\text{family of semantic false positives to the }(1-o)+\delta_1+\delta_2\text{ defect units.}
}
\]

At `S=Theta(n/log log n)`, proving that each defect unit can absorb only `O(log log n)` appropriately chosen semantic witnesses would yield the desired `Omega(n)` distinct-witness statement. For the fractional-transversal target, even weaker weighted incidence control may suffice; congestion is not intrinsically required there.

The key point is that **the structural denominator is now exact**. We no longer need to guess what a “slack unit” means in the pathology-free regime.

---

## 6. Small computational hostile check

As a sanity check on one extremal equality topology, I exhaustively propagated all 16 possible `B_2` truth tables along the chain family where each side variable is read exactly twice, deduplicating reachable Boolean functions and all possible read schedules.

- For `n=4`, 4,160 final functions were reachable; none matched the CLY obstruction labels on every assignment.
- For `n=5`, 255,488 final functions were reachable; none matched all CLY labeled layers.

This is discovery/falsification evidence only. It neither classifies all equality topologies nor proves the equality case. It is useful because it failed to find an immediate counterexample to Corollary 4.9 inside the simplest tight family.

---

## 7. Barrier and model audit

The conservation theorem is a finite graph/wire identity and relativizes. It is a bottleneck/stability lemma, not a nonrelativizing separation.

It defines no large constructive truth-table property, so it is not itself a Razborov--Rudich natural proof. Any eventual black-box property at the `2n+o(n)` PRF frontier still has to respect the Fan--Li--Yang natural-proof barrier.

No arithmetization occurs; no algebrization barrier is crossed. Missing-String/range-avoidance variants remain subject to the newer Chen--Hu--Ren audit.

The entire statement is in the unrestricted fan-in-two `B_2` model. No DeMorgan/formula/`U_2` lower bound is imported.

---

## 8. Provenance

Primary sources inspected on 2026-08-13:

- Zhiyuan Fan, Jiatu Li, Tianqi Yang, *The Exact Complexity of Pseudorandom Functions and the Black-Box Natural Proof Barrier for Bootstrapping Results in Computational Complexity*, ECCC TR21-125 rev. 1, especially Lemma 7.4 and Theorems 7.5--7.6.
- Lijie Chen, Jiatu Li, Tianqi Yang, *Extremely Efficient Constructions of Hash Functions, with Applications to Hardness Magnification and PRFs*, CCC 2022, LIPIcs 234:23, Section 4.4, Lemmas 4.7--4.10 and Corollaries 4.9, 4.11. The ECCC TR22-086 rev. 1 contains the same argument.

No claim here relies on a DeMorgan or formula lower bound.

FIVE-ALARM: OFF.