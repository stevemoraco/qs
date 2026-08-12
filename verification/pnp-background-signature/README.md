# Public verifier: PNP background-signature finite core

Date: 2026-08-12

Status: **finite combinatorial helper only; not P versus NP.**

This directory independently replays the canonical finite artifacts from the private research repository `stevemoraco/RH-Lean`.

Canonical private branch:

`agent/grand-engine-round203-background-incidence-20260811`

Canonical private Lean blob:

`e0d573ff3f1a1ed5687ea5071a16c09d8dbddccc`

Canonical private Python blob:

`0fedb6130c4a5177c1a895868f4d38de6b096806`

The Lean file proves only:

1. a finite map whose fibers have cardinality at most `q` has domain cardinality at most `q` times the codomain cardinality;
2. an `s`-bit signature with congestion at most `q` represents at most `q * 2^s` backgrounds;
3. if there are more than `q * 2^s` backgrounds, some signature fiber has cardinality greater than `q`;
4. the corresponding scalar contradiction.

The Python certificate checks the separate exact intersection-count identity and finite partition/pigeonhole implementations over the committed test range.

The workflow verifies Git blob identity before execution, rejects placeholders/custom trust declarations, compiles under Lean 4.31.0 with Mathlib v4.31.0, records all emitted axiom reports, and uploads replay evidence.

Not formalized or proved here:

- Boolean circuit syntax or semantics;
- critical paths or branching excess;
- the simultaneous-background circuit-capacity theorem;
- hardness magnification;
- the official definitions or separation of `P` and `NP`.

Five-alarm status: **OFF**.
