# RH B53G height-one factorial terminal: public kernel mirror

Date: 2026-08-13

Status: **finite terminal algebra only. Not RH. Six-alarm off.**

This directory mirrors the standalone Lean package from:

- repository: `stevemoraco/RH-Lean`
- source branch: `automation/rh-b53-bober-height-one-terminal-20260813-gpt56`
- source commit: `beda10cc0dc01627486f7e292bbb700855f470c6`
- source file: `RHB53/HeightOneBoberTerminal.lean`

The source-classification boundary is intentionally external to this Lean file. Jonathan W. Bober's Theorem 1.2 classifies primitive integral factorial ratios of height one into three infinite families and 52 sporadic cases. A separate human audit of Bober's sporadic table bounds every listed coefficient by 30, and separate human arguments supply the entropy lower bounds for the three infinite families.

The kernel package checks only the terminal consequences once those source inputs are supplied:

- the rational repeat-tax bound `1 / 992` for a period parameter at most 30;
- the exact comparisons with `log 2` and `(log 3) / 2` using Mathlib's certified logarithm bounds;
- the final three-way case split;
- exclusion of height one below `1/2 + 1/992` and the eventual height-at-least-two consequence;
- the scale-versus-maximum-coefficient lemma;
- the elementary dyadic-component geometry used in the second infinite family.

It does **not** formalize Bober's classification, the 52-row table audit, the infinite-family entropy estimates, Landau's criterion, the B53 factorial-ratio construction, the Nyman–Beurling equivalence, the zeta function, or RH.

Pinned environment:

- Lean `v4.19.0`
- Mathlib `v4.19.0`

A successful workflow certifies only that this finite package compiles under the pinned kernel, that the printed theorem axiom reports contain only the accepted imported foundations visible in the output, and that the source contains no forbidden proof-hole tokens. It is not a Clay-proof certificate.
