# Navier–Stokes — frequency-index multiplicity obstruction in arXiv:2601.15685v1

Date: 2026-08-13 UTC  
Primary source audited: Myong-Hwan Ri, *Global regularity for the Navier–Stokes equations with application to global solvability for the Euler equations*, arXiv:2601.15685v1 (2026-01-22), equations (2.2), (3.1), (3.8), and (3.11)–(3.15).

**Status:** PROVED exact arithmetic counterexample to equation (3.12); this kills the displayed averaging step that feeds (3.14)–(3.15); NOT a Navier–Stokes counterexample; FIVE-ALARM OFF.

## 1. Source definitions

The paper defines the sparse frequency weight

\[
a(j)=\log_2 j
\]

when

\[
j=i+2^{2^m}
\quad\text{for some }m\in\mathbb N,\ -m\le i\le m,
\]

and `a(j)=1` otherwise. It then defines

\[
b(j)=2^{-j-1}\sum_{i=1}^j2^ia(i).
\tag{1.1}
\]

The cutoff index is

\[
j_0(k)=\lceil\log_2k\rceil+1,
\]

so

\[
j_0(2k)=\lceil\log_2k\rceil+2.
\tag{1.2}
\]

After summing the frequency estimates, the proof needs

\[
\sum_{k=1}^n b(j_0(2k))\le3n.
\tag{1.3}
\]

This is equation (3.12) of the source. For exceptional shell labels, its displayed proof bounds the sum by

\[
|S(\lceil\log_2n\rceil+2)|
\max_{k\le n,\,j_0(2k)\in S}
b(j_0(2k)).
\tag{1.4}
\]

Formula `(1.4)` counts distinct exceptional shell labels but omits the number of cutoff indices `k` mapped to each label.

## 2. Exact multiplicity

For every integer `J>=3`, equation `(1.2)` gives

\[
j_0(2k)=J
\quad\Longleftrightarrow\quad
2^{J-3}<k\le2^{J-2}.
\tag{2.1}
\]

Hence one shell label `J` is repeated exactly

\[
2^{J-3}
\tag{2.2}
\]

times among the cutoff indices.

## 3. Central exceptional shells

Fix `m` and put

\[
J_m=2^{2^m}.
\]

This is the center of one of the source's exceptional windows, so

\[
a(J_m)=\log_2J_m=2^m.
\tag{3.1}
\]

The final summand in `(1.1)` alone gives

\[
b(J_m)
\ge
2^{-J_m-1}2^{J_m}a(J_m)
=2^{m-1}.
\tag{3.2}
\]

Now set

\[
n_m=2^{J_m-2}.
\]

By `(2.1)`–`(2.2)`, exactly `2^{J_m-3}=n_m/2` integers `k<=n_m` satisfy `j_0(2k)=J_m`. Their contribution to the left side of `(1.3)` is therefore at least

\[
\frac{n_m}{2}b(J_m)
\ge
\frac{n_m}{2}2^{m-1}
=2^{m-2}n_m.
\tag{3.3}
\]

Thus

\[
\boxed{
\frac1{n_m}\sum_{k=1}^{n_m}b(j_0(2k))
\ge2^{m-2}\longrightarrow\infty.
}
\tag{3.4}
\]

For every `m>=4`, `(3.3)` is strictly larger than `3n_m`. Since `n_m->infinity`, there is no generic `n_0` after which equation (3.12) holds.

## 4. Consequence for the claimed proof

Equation (3.12) is used together with the analogous odd-index estimate (3.13) to obtain (3.14), which is then substituted into the differential estimate (3.15). The even-index estimate already fails, so the displayed derivation of (3.14)–(3.15) is invalid.

The error is not a missing constant. The average grows at least like `2^{m-2}` along the explicit sequence `n_m`; no fixed linear constant repairs it.

A possible salvage would require a different frequency weight for which the pushforward multiplicities of `k -> j_0(2k)` are included in the averaging budget, or a genuinely weighted summation theorem replacing (3.12). That would alter the supercritical space and the later rescaling estimates and must be re-audited from the beginning.

## 5. Finite Lean model

The repository artifact `verification/ns-ri-frequency-multiplicity/NSRiFrequencyMultiplicity.lean` formalizes the finite combinatorial core:

- many cutoff indices map to one shell label;
- summing the repeated shell weight is not bounded by the number of distinct labels times the maximum weight;
- at the first decisive source ratio (`m=4`), `N` repetitions of weight `8` exceed the claimed `3n` budget when `n=2N`.

The Lean artifact deliberately does not formalize logarithms, the Navier–Stokes PDE, or Ri's full paper. The human derivation in Sections 1–3 supplies the exact source instantiation.

## 6. Hostile scope audit

- This refutes equation (3.12), not the Navier–Stokes equations.
- It does not exclude a fundamentally different proof of Ri's claimed theorem.
- The lower bound uses only the source's own definitions and one positive summand of `b(J_m)`.
- Every multiplicity and quantifier is explicit; no asymptotic density assumption is used.
- No Clay theorem is claimed.

\[
\boxed{\text{FIVE-ALARM OFF.}}
\]
