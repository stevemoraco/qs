# YM total-family finite detected-spectrum verifier

This verifier closes one finite spectral inference exactly.

Let a finite family of modes have energies `E j`. If every mode is detected
by some observable with strictly positive weight `A`, and the corresponding
mode contribution obeys

```text
A * exp (-E j * t) <= C * exp (-m * t)
```

for every nonnegative real `t`, with `C >= 0`, then `m <= E j`. Hence
finite coverage forces every listed energy to be at least `m`.

The scalar proof is constructive. Assuming `E < m`, it selects

```text
t = (C / A + 1) / (m - E)
```

and uses `1 + x <= exp x` to derive the strict reverse inequality at that
specific time. There is no passage to a limit.

## Why this matters

For an already-constructed self-adjoint Hamiltonian, the analogous infinite
statement can be proved detector by detector with spectral projections: a
total family whose individual correlations all have common exponent `m`
forces the spectrum on the generated sector into `[m, infinity)`. Uniform
frame lower bounds and summability of all prefactors are sufficient but are
not necessary for that inference.

This Lean file formalizes the finite detected-mode theorem only. It does not
formalize:

- construction of four-dimensional quantum Yang--Mills theory;
- Osterwalder--Schrader reconstruction;
- existence or self-adjointness of a continuum Hamiltonian;
- passage from a lattice regulator to the continuum;
- completeness/totality of a physical observable family;
- the infinite-dimensional spectral-projection argument;
- the official Clay Yang--Mills existence and mass-gap theorem.

Accordingly, successful verification is a finite firewall, not a Millennium
solution.

## Replay contract

The workflow pins Lean and Mathlib to `v4.32.1`, rejects explicit
placeholders and custom result carriers, compiles the exact source, records
its SHA-256, prints theorem axioms, rejects `sorryAx` and
`Lean.ofReduceBool` in compiler output, and uploads the evidence.
