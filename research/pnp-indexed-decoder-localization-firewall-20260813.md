# P versus NP block lift: normalized indexed-router firewall

**Date:** 2026-08-13  
**Status:** exact finite promise compiler and gate-count correction; **not a
circuit lower bound and not P versus NP**.  
**Base:** qs PR #191, head
699559cb55fc4a88f5b6bf65af9b481a21976cb9.

## 1. Provenance and correction

The indexed-router obstruction was already banked on branch
agent/gpt56-pnp-indexed-router-firewall-20260813-run2:

- human theorem commit
  e7256d86d600bb543bfca182e2662d1edeaa77b8;
- Lean arithmetic commit
  429317fe30c084721c401fb3b19b9f4ed78c127d;
- finite checker commit
  1e4d38d4f4f762ff677c86e0fd67e3320b733864;
- audited head
  347d92d539556142deae54a54f8b9d0475141968.

That bank gives the valid upper bound

\[
2N+k-b-2-r+d.
\]

A hostile reconstruction found two groups of dead gates in that displayed
construction. The result below is the correction; it is not a duplicate claim
of a new indexed-router idea.

## 2. Proposed bridge under audit

The current microhard block lift partitions \(N=kb\) input bits into \(k\)
blocks. Its load-bearing conjecture asks a near-\(2N\) unrestricted fan-in-two
DAG to have restricted complexity \(g_j(C)\leq 3b\) on enough blocks, charging
exceptions to the Fan--Li--Yang \(2N-2\) critical-path surplus.

Repeated local lists are already defeated by coordinatewise compression and a
shared decoder. Requiring the lists \(T_j\) to be distinct does not by itself
supply the missing direct-sum theorem: an indexed decoder can still share all
semantic work.

## 3. Exact partial-label compiler

Let \(z_j\) be the OR of the inputs in block \(j\). The compiler is required
only on the following finite labels:

- one-active-block words \(E_j(t)\) and \(E_j(h)\);
- global singleton positives;
- the all-ones positive.

It is **not** claimed here to decide arbitrary multi-active inputs or the full
Chen--Li--Yang obstruction.

Under the one-active-block promise:

1. compute occupancy only for blocks \(1,\ldots,k-1\), costing
   \((k-1)(b-1)\) gates;
2. compute the coordinatewise compressed payload, costing
   \(b(k-1)=N-b\) gates;
3. for \(k=2^r\), compute the binary block index with the explicit pruned
   dyadic-OR encoder, costing
   \[
   F(r)=2k-2-2r
   \]
   gates;
4. apply one shared indexed decoder \(D(j,y)\) of size \(d\).

Block zero needs no occupancy tree: its code is \(0^r\), so absence of positive
index bits already selects it. On \(E_0(w)\), the index is \(0^r\) and the
compressed payload is \(w\). On \(E_j(w)\) for \(j>0\), the index is
\(\operatorname{bin}(j)\) and the payload is \(w\). On \(1^N\), every positive
index bit and every payload bit is one.

Consequently the normalized construction ledger is

\[
\begin{aligned}
R
&=(k-1)(b-1)+b(k-1)+(2k-2-2r)+d\\
&=\boxed{2N+k-2b-1-2r+d}.
\end{aligned}
\]

The earlier expression exceeds this one by exactly \(b+r-1\) gates. If a
separate exact-one, any-active, or validity guard uses \(z_0\), then the
\(b-1\) block-zero occupancy gates must be restored and the semantic
requirement must be stated explicitly.

## 4. Encoder audit

In a complete dyadic OR tree on \(k=2^r\) leaves, delete the \(r\) internal
ancestors of leaf zero. Those left-prefix nodes feed no positive output bit.
The remaining dyadic source gates number

\[
T_r=k-1-r.
\]

Number output bits from most to least significant. The bit at level \(q\) is a
union of \(2^q\) available dyadic sources, so joining its sources costs
\(2^q-1\) gates. Thus

\[
M_r=\sum_{q<r}(2^q-1)=k-1-r,
\qquad
F(r)=T_r+M_r=2k-2-2r.
\]

Equivalently, with the internal dyadic sources exposed,

\[
F(0)=0,\qquad F(r+1)=2F(r)+2r,
\]
and the subtraction-free closed form is
\[
F(r)+2r+2=2^{r+1}.
\]

The first values are \(0,0,2,8,22,52\). This is the exact gate count of this
specific construction, hence an **upper bound** on encoder circuit complexity.
It is not a minimum-size theorem. Treating the recursive encoders as black
boxes would not justify the recurrence, because the construction reuses
exposed subtree signals.

## 5. Claimant, critic, rebuilder

**Claimant.** Distinct canonical local lists make block identity costly enough
that the Fan--Li--Yang surplus can be charged once per restricted block.

**Critic.** Distinctness is set-theoretic, not an indexed-decoder lower bound.
The compiler recovers the active word and its index with only
\(2N+O(k)\) front-end gates, then pays for \(D(j,y)\) once. Therefore no
general-DAG inequality charging the semantic restricted decoder independently
for every block follows from distinctness or from the \(2N-2\) wire ledger
alone.

**Small counterexample to identity-forces-direct-sum.** Take any family of
distinct, cheaply indexed local predicates. The construction above shares one
small indexed decoder even though every fixed-index restriction can present a
different predicate. Distinct block names alone do not force additive
restricted complexities.

**Best salvage.** The particular canonical good family from PR #191 is not
refuted. Its exhaustive construction proves polynomial-time uniformity in
\(N\), but that yields only a polynomial-size indexed decoder, not the needed
sub-frontier size. Conversely, no lower bound near the frontier is known for
that decoder.

If the target surplus is \(S(N)\), this partial-label compiler lies within
\(2N+S(N)\) whenever

\[
d\leq S(N)-k+2b+1+2r.
\]

The exact surviving bridge is therefore representation-sensitive:

> either construct a decoder of that size for the canonical partial tables,
> or prove a matching lower bound for
> \(D(j,y)=[y\in T_{b,j}]\).

That lower bound is not a consequence of pairwise distinctness, local
hard-core counting, or Fan--Li--Yang's topology alone.

## 6. Lean scope

PNPIndexedDecoderFinite.lean proves:

- coordinatewise propositional compression equals the active block under an
  exact one-active-block restriction;
- the subtraction-free recurrence identity for the pruned encoder count;
- the \(r\)-gate encoder saving;
- both the unnormalized and normalized integer router ledgers;
- the total \(b+r-1\) correction to the prior banked expression.

Lean does **not** yet construct or evaluate a Boolean DAG. A full formal
certificate would still require an OR-circuit datatype, a constructed network,
promise-correct evaluation, and a gate-count theorem. It also does not
formalize Fan--Li--Yang, Chen--Li--Yang, the canonical search, a decoder lower
bound, or the full target language.


## 7. Lean replay receipt

The exact Lean source with blob
2d164dc9338d9cf2164f6327e0ca087f1497cffa and SHA-256
aef70625aa541d6838ce56c4b3e38658f0f91acd7a00bd26ee70db0e540fa3f2
passed workflow run 31700968449, job 94449746727, under Lean 4.32.1,
Lake 5.0.0, and Mathlib v4.32.1.

Artifact 9181264966 has digest
sha256:b54b9f57622032b4e2968df7892b259e60508f124ff55d630a42d686f3dbdb1a.
The source trust scan found no sorry, admit, sorryAx, custom axiom, opaque,
unsafe, native_decide, or Lean.ofReduceBool. The printed theorem dependencies
are only propext, Classical.choice, and Quot.sound.

This receipt verifies the finite Lean statements listed in Section 6. It is
not evidence for an unformalized circuit construction or for P versus NP.

**SIX-ALARM: OFF.**
