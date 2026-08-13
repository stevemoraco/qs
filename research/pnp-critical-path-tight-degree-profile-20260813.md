# P versus NP braid: exact degree profile at the `2n-2` critical-path boundary

Date: 2026-08-13
Parent result: `research/pnp-critical-path-slack-conservation-20260813.md`
Status: finite structural sharpening; **not** a circuit lower bound and not P-vs-NP.

## Result

The exact slack identity already banked says that every normalized,
single-output, pathology-free unrestricted fan-in-two `B_2` circuit satisfies

\[
|G|-(2n-2)=(1-o)+\delta_1+\delta_2,
\]

where `o in {0,1}` indicates whether the output lies on a critical path and
`delta_1,delta_2>=0` are the exact Type-1 and Type-2 outgoing-wire excesses.

At the exact boundary `|G|=2n-2`, all three terms vanish:

\[
o=1,\qquad \delta_1=0,\qquad \delta_2=0.
\]

Keeping the meaning of those zero excesses, rather than only their scalar
sum, gives a rigid **out-degree profile**:

\[
\boxed{
\begin{array}{ll}
\text{unique output:} & \deg^+=0,\\
\text{the other }n-1\text{ critical-path endpoints:} & \deg^+=2,\\
\text{every non-endpoint Type-1 node:} & \deg^+=1,\\
\text{every Type-2 node:} & \deg^+=1.
\end{array}}
\]

Thus an equality-tight pathology-free circuit has exactly `n-1` branching
nodes, each of fan-out exactly two. Every other non-output node has fan-out
exactly one.

This is stronger than the previously banked scalar statement and gives a
much smaller equality-case search space for the Chen--Li--Yang boundary audit.

## Derivation

Let `c1,c2` be the Type-1/Type-2 node counts and let `l` be the number of
Type-1-to-Type-1 wires, using the definitions in the conservation note.

Because the critical paths are pairwise disjoint, exactly `c1-n` Type-1
nodes are non-endpoints on their critical paths. By definition each such node
has out-degree exactly one. There are exactly `n` path endpoints. When `o=1`,
one endpoint is the unique output and has out-degree zero; every other endpoint
is a non-output normalized node whose critical path stopped because its
out-degree is not one, and the no-isolated/pathology assumptions give the
Fan--Li--Yang lower bound of at least two outgoing wires there.

Therefore the Type-1 total outgoing degree is at least

\[
(c_1-n)+2(n-1)=c_1+n-2.
\]

By definition

\[
\delta_1
=W_{12}-(c_1+n-2-l),
\]

so

\[
l+W_{12}=c_1+n-2+\delta_1.
\]

At equality `delta_1=0`, the total outgoing degree attains the lower bound
exactly. Since every individual contribution is already at least its displayed
minimum, every one of the `n-1` non-output path endpoints has out-degree
**exactly two**. No Type-1 node has any extra outgoing degree beyond the
critical-path minimum.

For Type 2, the exact definition is

\[
\delta_2=(W_{21}+W_{22})-(c_2-(1-o)).
\]

At the boundary `o=1`, every Type-2 node is a non-output normalized node, so
its out-degree is at least one. Since `delta_2=0`, their total outgoing degree
is exactly `c2`; hence every Type-2 node has out-degree **exactly one**.

No assumption that `l=c1-n` is used here. In particular, Type-1-to-Type-1
cross-wires not themselves lying along a critical path are not silently
excluded. The statement is only the exact degree profile forced by tightness.

## Why this matters for the equality-boundary audit

The published CLY obstruction uses the six Hamming layers

\[
|x|\in\{0,1,2,n-2,n-1,n\}
\]

with labels `0,1,0,0,0,1`, respectively. Their path-intersection lemma handles
circuits with intersecting critical paths; isolated inputs are also immediately
incompatible with perfect completeness on all weight-one inputs. The displayed
wire-count lemma only gives `>=2n-2`, so the pathology-free equality class is
the remaining boundary case isolated in the conservation note.

The degree profile above says that class is not an arbitrary `2n-2`-gate DAG.
It is a minimum-fanout network with exactly `n-1` binary branch events and no
other fanout surplus. Any equality-case semantic proof can therefore target
those `n-1` branch nodes directly.

A useful equivalent semantic signature of the CLY labels is obtained from
Boolean derivatives over `F_2`. If `f` agrees with the obstruction labels,
then for every `i != j`,

\[
D_i f(0)=D_i f(1)=1,
\]

while the off-diagonal second derivatives satisfy

\[
D_iD_j f(0)=0,\qquad D_iD_j f(1)=1.
\]

Indeed the low-corner four values are `0,1,1,0`, whereas the high-corner four
values are `1,0,0,0`. This derivative reformulation is exact and suggests a
new equality-case target:

> prove that a normalized pathology-free `2n-2`-gate network with the rigid
> degree profile above cannot switch **all** pairwise mixed derivatives from
> zero at the low corner to one at the high corner while keeping every first
> derivative equal to one at both corners.

No such semantic theorem is claimed here. The derivative signature is a
reparameterization of the six-layer labels, not an additional assumption.

## Claimant / critic / rebuilder

**Claimant.** Tightness should force a read-twice/formula-like semantic
collapse, making the derivative switch impossible.

**Critic.** The degree profile alone does **not** imply a formula. The `n-1`
fan-out-two endpoints permit sharing, and Type-1-to-Type-1 cross-wires are not
excluded. One branch can influence many input pairs, so a naive
`binom(n,2)`-pairs-versus-`n-1`-branches count is invalid.

**Rebuilder.** Search for a per-branch invariant that survives sharing: e.g.
rank/support of the low/high Boolean Hessian difference, a cut-rank quantity,
or a finite two-corner influence matrix whose change across a binary gate is
subadditive and whose total capacity is exactly charged by branch excess. Any
such invariant must be proved in unrestricted `B_2`, not imported from
formulas or DeMorgan circuits.

## Frontier extension

For `|G|<=2n+S`, the banked conservation theorem gives only `S+2` total defect
units beyond the baseline. The equality profile suggests the stability version
we actually want:

\[
\boxed{
\text{baseline }(n-1)\text{ binary branches}
+\text{ at most }S+2\text{ excess-degree units}.}
\]

If one can prove that each excess unit can repair only `O(log log n)` of a
carefully selected family of derivative/witness constraints, the requested
`Omega(n)` semantic witness theorem at
`2n+O(n/log log n)` becomes plausible. This is exactly where the finite
structural ledger and the semantic hard-core target now meet.

## Model and barrier audit

- The degree-profile theorem is finite graph arithmetic and relativizes.
- It creates no large constructive truth-table property; it does not itself
  evade natural proofs.
- It uses no arithmetization and does not evade algebrization.
- Every gate is an arbitrary binary Boolean function in the unrestricted
  `B_2` DAG model with arbitrary fan-out.
- No formula/read-once/read-twice conclusion is asserted.
- The CLY equality boundary remains **open in this repository** until a semantic
  theorem covers this tight degree-profile class or an explicit counterexample
  is found.

Primary provenance: Fan--Li--Yang, ECCC TR21-125 rev. 1, Lemma 7.4 and
surrounding critical-path definitions; Chen--Li--Yang, ECCC TR22-086 rev. 1 /
CCC 2022, Lemmas 4.7--4.8 and Corollary 4.9, audited 2026-08-13 in the parent
research note.

FIVE-ALARM: OFF.
