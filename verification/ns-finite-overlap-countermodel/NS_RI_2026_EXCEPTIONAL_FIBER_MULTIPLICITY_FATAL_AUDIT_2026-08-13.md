# Ri 2026 global-regularity claim: exceptional-fiber multiplicity obstruction

**Date:** 2026-08-13  
**Primary source:** Myong-Hwan Ri, *Global regularity for the Navier-Stokes equations with application to global solvability for the Euler equations*, arXiv:2601.15685v1, submitted 2026-01-22.  
**Audited location:** Section 3, equations (3.1), (3.5), and (3.8)–(3.14).  
**Status:** fatal obstruction to the printed proof; not a proof or disproof of the Clay theorem.

## 1. Role of the disputed estimate

The manuscript defines sparse frequency weights

\[
a(j)=\log_2j
\]

on short windows around the indices

\[
m_r=2^{2^r},
\]

and sets

\[
b(j)=2^{-j-1}\sum_{i=1}^j2^ia(i).
\]

After testing the Navier–Stokes equation against high-frequency tails, the proof obtains a factor

\[
b(j_0(k)),
\qquad
j_0(k)=\lceil\log_2k\rceil+1.
\]

The higher-order energy superposition requires a uniform linear average of these factors. In particular, the manuscript claims

\[
\sum_{k=1}^n b(j_0(2k))\le 3n.
\tag{R3.12}
\]

This estimate feeds directly into (3.14), (3.15), the integrated estimate (3.16), and ultimately the rescaled absorption argument (3.24)–(3.30).

## 2. The exact invalid inference

The exceptional contribution is written as

\[
\sum_{\substack{k\le n\\
j_0(2k)\in S(M)}}b(j_0(2k)),
\qquad
M=\lceil\log_2n\rceil+2.
\]

The manuscript bounds this by

\[
|S(M)|
\max_{\substack{k\le n\\j_0(2k)\in S(M)}}b(j_0(2k)).
\tag{*}
\]

Inequality `(*)` would be valid for a sum indexed once by the distinct image values in `S(M)`. It is not valid for a sum over all threshold indices `k`. The map

\[
k\longmapsto j_0(2k)=\lceil\log_2k\rceil+2
\]

is exponentially many-to-one. Every image value must be multiplied by the cardinality of its fiber.

The correct regrouping is

\[
\sum_{\substack{k\le n\\j_0(2k)\in S(M)}}b(j_0(2k))
=
\sum_{j\in S(M)}
\#\{k\le n:j_0(2k)=j\}\,b(j).
\]

The omitted multiplicity is precisely what destroys the desired linear bound.

## 3. Exact source-specific counterexample

Fix an integer `r>=4` and put

\[
m=2^{2^r},
\qquad
n=2^{m-2}.
\]

At the center of the `r`-th sparse window,

\[
a(m)=\log_2m=2^r.
\]

The last term in the exponentially weighted average defining `b(m)` gives

\[
\begin{aligned}
b(m)
&=2^{-m-1}\sum_{i=1}^m2^ia(i)\\
&\ge 2^{-m-1}2^ma(m)\\
&=\frac12a(m)
=2^{r-1}.
\end{aligned}
\tag{1}
\]

Now consider all integers

\[
2^{m-3}<k\le2^{m-2}=n.
\]

There are exactly

\[
2^{m-2}-2^{m-3}=2^{m-3}=\frac n2
\]

such values, and each satisfies

\[
\lceil\log_2k\rceil=m-2,
\qquad
j_0(2k)=m.
\tag{2}
\]

Moreover,

\[
M=\lceil\log_2n\rceil+2=m,
\]

and the center `m` belongs to the exceptional set `S(M)` by its definition.

Therefore the exceptional sum alone obeys

\[
\begin{aligned}
\sum_{\substack{k\le n\\j_0(2k)\in S(M)}}b(j_0(2k))
&\ge \frac n2 b(m)\\
&\ge 2^{r-2}n.
\end{aligned}
\tag{3}
\]

For `r=4`, this is at least

\[
4n.
\]

It contradicts both the manuscript's exceptional estimate by `n` and the total estimate (R3.12) by `3n`. No asymptotic choice of `n_0` repairs the failure, because the same contradiction occurs at every sufficiently large sparse center.

## 4. Structural incompatibility

The obstruction is stronger than one failed constant.

Suppose a uniform averaging estimate

\[
\sum_{k=1}^n b(j_0(2k))\le Cn
\]

held for every sufficiently large `n`. At `n=2^{m_r-2}`, the final dyadic fiber occupies half of the whole prefix. Hence

\[
\frac n2 b(m_r)\le Cn,
\]

so

\[
b(m_r)\le2C.
\tag{4}
\]

But (1) gives

\[
b(m_r)\ge\frac12a(m_r)=2^{r-1}\to\infty.
\tag{5}
\]

Thus the two load-bearing design requirements are incompatible:

\[
\boxed{
\begin{aligned}
&\text{unbounded sparse weights needed for rescaling-smallness},\\
&\text{uniform linear averaging over integer thresholds needed for absorption}.
\end{aligned}}
}
\]

The exponential fibers of `j_0` convert every large shell spike into a positive-density block of threshold indices.

## 5. Consequence for the theorem

Equations (3.12) and (3.13) are used to derive (3.14), which is inserted into the high-frequency energy inequality (3.10). Without the claimed linear average, the coefficient in front of the critical dissipation is not uniformly bounded. The subsequent choice

\[
\varepsilon=\frac{\nu}{4C_3}
\]

and rescaled absorption cannot be justified with the printed constants.

Therefore Theorem 1.1 and the Euler corollary are not proved by the manuscript.

This conclusion does not establish singularity, disprove global regularity, or rule out a completely different proof.

## 6. Best salvage

A repair must change the summation architecture, not a constant. Possible directions include:

1. superpose over logarithmic shell index with the correct shell-width measure rather than count every integer threshold equally;
2. insert reciprocal fiber multiplicities before summation and rederive the Sobolev equivalence;
3. replace the sparse unbounded weight by a different norm whose scaling-smallness and threshold averaging are proved simultaneously.

Each option changes the energy functional and all estimates downstream of (3.10). The current `a,b,j_0` construction cannot satisfy both properties.

There is also a separate apparent typographical mismatch in the second identity of (3.17): the left side omits the displayed `k^s` weight while the right side retains it and replaces gradient annuli by velocity annuli. Correcting that line does not affect the multiplicity obstruction above.

## 7. Lean firewall

File: `NavierStokesRiExceptionalFiberFirewall.lean`.

The formal declarations prove:

- a weight repeated on `N` preimage points contributes `N*B`;
- one-point image cardinality does not bound a positive sum on a nontrivial fiber;
- a linear bound on a half-prefix fiber forces the fiber weight to be uniformly bounded;
- spike floor `A/2` plus a uniform linear average forces `A<=4C`;
- weight eight on a half-prefix block already exceeds `3n`;
- an explicit four-to-one finite image countermodel.

The Lean file formalizes only finite multiplicity and scalar inequalities. The source-specific identification of the dyadic fiber and the lower bound `b(m)>=a(m)/2` are proved above at the human level.

## 8. Claim / counterexample / best salvage

**Claim:** The sparse exceptional set has sufficiently small cardinality to imply the linear threshold average (3.12).

**Counterexample:** One exceptional shell index has an exponentially large threshold fiber. At the fourth sparse center its repeated contribution is at least `4n`, already larger than the claimed total `3n`.

**Best salvage:** Replace image-cardinality counting by exact fiber-weighted counting and redesign the superposition norm. Under the current unbounded spikes, exact fiber counting proves a no-go rather than the required estimate.

## Status

No official Navier–Stokes theorem or disproof is obtained. The manuscript's claimed global-regularity proof is invalid at a finite combinatorial step. SIX-ALARM remains off.
