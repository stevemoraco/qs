# Independent public replay — BSD semiprime density finite core

This directory mirrors the exact finite Lean source in `stevemoraco/RH-Lean`
PR #814, commit `db23311fd5ae2244a2b708ae61485b0d43c1a8e6`.

It exists to obtain an independent public-repository GitHub Actions replay
because the private repository runner failed before executing any workflow
step, as did an unrelated control PR.

The source proves only the finite 128-state congruence/sign count,
quadratic-reciprocity transport, row counts, and rational coefficient
certificates. It does not formalize the quadratic large sieve, prime number
theorem, Selmer theory, CM rank-zero converse, complete CM BSD theorem, or the
official Clay conjecture.
