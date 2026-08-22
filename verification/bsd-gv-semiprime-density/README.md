# BSD Ghosh–Voutier semiprime density verifier

Status: **FINITE CORE ONLY — NOT A BSD OR CLAY PROOF**

This directory formalizes the finite residue/sign spine of a human arithmetic-statistics theorem for

```text
E_{p,q}: y^2 = x^3 - pq x,
```

with distinct odd primes `p,q`.

## Human theorem packet

The companion research note is in `stevemoraco/RH` PR #93. Its primary arithmetic interfaces are:

- Ghosh–Voutier, arXiv:2607.14033v1, Theorems 1.1–1.2;
- Burungale–Tian, arXiv:2506.03465v1, Theorem 1.1, applied at `p=2`;
- Burungale–Flach, arXiv:2206.09874v3, Corollary 2;
- Zhang–Diao, arXiv:2608.10702v1, Lemma 2.1 and Proposition 2.3, for the corrected `j=1728` root-number formula.

For odd squarefree `D`, Zhang–Diao specialize to

```text
W(y^2=x^3-Dx)=+1
iff
D=1,3,11,13 mod16.
```

The Lean file encodes only that finite residue shell. It does not formalize the local root-number theorem.

## Modules

### `BSDGVSemiprimeDensity.lean`

Certifies:

- `128` total residue/sign states;
- `64` ordered residue pairs;
- `28` accepted states;
- row spectrum `3,5,3,3,3,5,3,3`;
- `4/24` positive/negative Legendre-sign split;
- exact both-sign pair classification `(3,11),(11,3)`;
- reciprocity transport symmetry;
- the generic theorem that every mod-16-only guaranteed selector has at most two pairs;
- coefficient identities `7/32`, `1/32`, and `3/16`.

### `BSDGVAsymptoticAggregation.lean`

Certifies only the finite-sum limit wrapper:

```text
statewise mass -> 1/128
=>
accepted mass -> 7/32.
```

It does not prove statewise prime-pair equidistribution.

### `BSDGVDiscriminantHeight.lean`

Certifies the exact polynomial and rational coefficient algebra behind

```text
Delta=64D^3,
7/32 natural density -> 21/128 discriminant-height coefficient.
```

It does not prove that the displayed integral model is minimal. The human proof uses the standard discriminant transformation law: every local discriminant valuation is `0`, `3`, or `6`, hence is below `12` and cannot be lowered by a positive multiple of `12`.

### `BSDGVRootNumberSpectrum.lean`

Certifies the finite consequences of the corrected root-number shell:

- `64` positive-root-number states;
- every accepted state lies in that sector;
- exact accepted product-residue counts `4,8,0,0,0,8,8,0` for residues `1,3,5,7,9,11,13,15`;
- classwise certified coverage `1/4` in residue `1` and `1/2` in residues `3,11,13`;
- zero accepted states in every negative-root-number residue class;
- `28/64=7/16` certified share of the positive-root sector;
- `4/64=1/16` pure residue-only core;
- `24/64=3/8` character-sensitive increment;
- exact sevenfold gain from retaining the Legendre bit;
- minimal-discriminant coefficient identities.

## What Lean does not formalize

The following remain explicit external human theorems or proofs:

```text
primality and Legendre symbols;
quadratic reciprocity as number theory;
PNT and Mertens in arithmetic progressions;
Siegel–Walfisz;
primitive-character or quadratic large sieve;
Ghosh–Voutier descent;
Selmer exact sequence for elliptic curves;
Burungale–Tian rank-zero p-converse;
Burungale–Flach complete CM BSD;
Zhang–Diao local/global root-number formula;
minimality of the Weierstrass equation;
the official Clay BSD statement.
```

## Workflow gates

The pinned workflow builds every module, replays each source directly, prints every theorem through `AxiomReport.lean`, and rejects:

```text
sorry
admit
sorryAx
custom axiom
opaque
unsafe
native_decide
Lean.ofReduceBool
```

The accepted foundation-only axiom set is

```text
{propext, Classical.choice, Quot.sound}.
```

The initial failed replays, coercion repair, and later successful receipts are preserved in the PR history. The latest source must not be called verified until its own head has a successful replay and full axiom report.

SIX-ALARM: OFF.
