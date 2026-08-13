# Perfect completeness does not force residual shattering

**Date:** 2026-08-13  
**Status:** GREEN finite-support and counting no-go; no \(P\ne NP\) consequence.  
**Scope:** one-sided probabilistic formulas, sparse MCSP target sets, and the CKLM/CJW local-PRG interface. This does not rule out a new non-black-box generator with a substantially richer residual support.

## 1. Finite-support perfect-completeness firewall

Let \(\mathcal A\) be a distribution on deterministic Boolean formulas such that

- \(\Pr_{A\sim\mathcal A}[A(y)=1]=1\) for every YES input \(y\);
- \(\Pr_{A\sim\mathcal A}[A(x)=1]\le\eta\) for every NO input \(x\).

Fix a restriction \(\rho\) with a set \(S\) of \(k\) live coordinates, and a filler
\[
G:\{0,1\}^r\to\{0,1\}^{S}
\]
such that every completion \(\rho\circ G(z)\) is a YES input.

### Theorem 1.1

1. With \(\mathcal A\)-probability one, one and the same deterministic formula \(A\) accepts every \(\rho\circ G(z)\).
2. The support of \(G(U_r)\) has size at most \(2^r\).
3. If \(r<k\), \(G(U_r)\) cannot shatter \(S\), and
   \[
   \operatorname{TV}(G(U_r),U_S)\ge1-2^{r-k}.
   \]

**Proof.** Each of the finitely many \(2^r\) YES completions is accepted on a probability-one event. Their finite intersection still has probability one. The support statement is immediate. If \(T=\operatorname{supp}(G(U_r))\), then \(U_S(T)=|T|/2^k\le2^{r-k}\), while \(G(U_r)(T)=1\). \(\square\)

In fact, at any fixed input length perfect completeness is simultaneous over the entire finite YES set, by the same finite-intersection argument. This still does not create new truth-table patterns.

### Smallest semantic counterexample

Let
\[
\mathrm{YES}=\{x:x_1=0\},\qquad
\mathrm{NO}=\{x:x_1=1\},
\]
and use the deterministic perfect-complete formula \(A(x)=\neg x_1\). A point mass on one YES string has perfect completeness and zero soundness error but shatters no nontrivial coordinate set. Thus even zero soundness does not imply support richness.

## 2. Circuit-table counting

Fix a finite Boolean gate basis of cardinality \(b\), fan-in at most two. A Boolean function on \(m\) inputs computed by at most \(L\) gates has at most
\[
C(m,L)\le (L+1)M[bM^2]^L,\qquad M=m+L+2,
\]
possible circuit descriptions. Constants are the two extra sources; overcounting gates, predecessor pairs, and output nodes is harmless.

Consequently the entire set of size-\(L\) truth tables cannot shatter \(k\) fixed addresses unless
\[
2^k\le C(m,L),
\]
or equivalently
\[
k=O\!\left(L\log(m+L+b)\right).
\]

A lookup circuit gives the matching scale up to logarithms: arbitrary payloads on \(q\) fixed \(m\)-bit addresses can be realized with \(O(qm)\) gates.

## 3. MCSP-specific obstruction

Let the truth-table length be \(n=2^m\), and let the YES set be
\[
\mathrm{MCSP}[n^\alpha].
\]
The number of YES truth tables is at most
\[
2^{O(n^\alpha\log n)}.
\]

In the Chen–Jin–Williams Theorem 5.5 restriction regime, the number of live positions is
\[
k\ge n^{\alpha+\varepsilon/5}.
\]
Therefore
\[
\log_2|\mathrm{MCSP}[n^\alpha]|
 =O(n^\alpha\log n)
 =o(k).
\]
Even the complete YES set has strictly fewer than \(2^k\) residual patterns and misses almost all payloads on those live coordinates.

Hence the strongest possible use of perfect completeness—one deterministic realization accepting every YES instance simultaneously—still does not expose a residual cube.

## 4. The actual CKLM support mismatch

In the same CJW proof, the residual formula size is
\[
s=n^{3\alpha-3\varepsilon/5+o(1)}.
\]
The CKLM local PRG has seed length and local output complexity
\[
s^{1/3+o(1)}
 =n^{\alpha-\varepsilon/5+o(1)}.
\]
Write this seed length as \(r\). Since
\[
r=o(k),
\]
its residual distribution has support at most \(2^r\), cannot shatter the \(k\) live positions, and obeys
\[
\operatorname{TV}(G(U_r),U_k)
 \ge1-2^{r-k}\longrightarrow1.
\]

There is no contradiction with CKLM/CJW: their generator only needs to fool the specified residual formula class with constant error (in CJW, \(0.1\)). Constant-error computational indistinguishability is far weaker than atomwise exact-pattern fooling or total-variation proximity.

## 5. Claim / counterexample / salvage

**Failed claim.** Atserias–Müller one-sided perfect completeness plus a CJW residual restriction forces exact payload exposure, allowing shattering to cross the cubic \(1/3\)-locality gate.

**Counterexample.** The entire \(\mathrm{MCSP}[n^\alpha]\) YES class itself has only
\[
2^{O(n^\alpha\log n)}<2^{n^{\alpha+\varepsilon/5}}
\]
patterns on the CJW live set. The CKLM generator support is smaller still.

**Best salvage.** Perfect completeness removes a union-bound loss over any *pre-existing finite generator support*: a deterministic sampled formula can accept all those generated YES completions simultaneously. It neither enlarges that support nor supplies atomwise or total-variation control.

A successful bridge would need an additional theorem producing at least one of:

1. residual support of size \(2^k\);
2. atomwise exact-pattern error \(<2^{-k}\);
3. nontrivial total-variation control on the live cube;

while retaining locality strictly below the CKLM \(s^{1/3+o(1)}\) scale. That is the unresolved cubic bridge, not a consequence of one-sided semantics.

## 6. Exact source quantifiers

- Atserias–Müller, arXiv:2503.24061v2: PFML has acceptance probability \(1\) on each YES instance and at most \(1/4\) on each NO instance (pp. 2–3). Their Theorem 24 uses \(c\in\mathbf N\), \(\delta,\varepsilon>0\), \(\gamma<\delta/c\), and a \(2^{n^\gamma}\)-sparse \(Q\in NP\). At \(c=3\), the exponent gate is strict: \(\gamma<\delta/3\).
- Chen–Jin–Williams, ECCC TR20-065 (2020): Definition 1.1 is two-sided \(2/3\); Theorem 5.3 records the CKLM \(s^{1/3+o(1)}\) seed/local-output scale; Theorem 5.5 supplies the live-coordinate and residual-size exponents above and uses constant-error expectation fooling.
- Cheraghchi–Kabanets–Lu–Myrisiotis, ICALP 2019 / ToCT 2020: the corresponding local-PRG definitions and locality theorem have the same fixed-seed computational-fooling interface.

This note proves an exact architecture-level no-go only. It neither strengthens the known formula lower bound nor proves \(P\ne NP\). No Lean compilation or axiom audit has been performed.
