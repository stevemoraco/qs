# Public verifier — RH confluent arithmetic-grid block symbol

**Status:** finite symbolic and numerical replay only. **Not** RH, not a theorem about zeta-zero spacing, and not a formal proof of the infinite block-Toeplitz theorem.

## Canonical private provenance

- Repository: `stevemoraco/RH-Lean`
- Branch: `agent/rh-confluent-grid-block-symbol-20260812`
- Private mathematical note: `scratch/rh_braid/RH_CONFLUENT_ARITHMETIC_GRID_BLOCK_SYMBOL_2026-08-12.md`
- Exact private script blob: `99fe1c045c28ae713c63921624ba89ed4030f9d9`

## Replayed checks

The Python certificate checks:

1. the geometric Hankel moment determinant symbolically for `m=1,...,5`;
2. the exact block-symbol determinant in 48 high-precision cases;
3. positivity and the explicit determinant/trace lower floor in those cases;
4. 48 finite block-section spectra against the same dimension-free floor and ceiling.

Default replay parameters:

- multiplicities `1,2,3,4`;
- ratios `0.05,0.15,0.4`;
- four symbol phases;
- section lengths `1,2,5,10`;
- 70 decimal digits;
- symbol-series tail threshold `1e-60`.

The privately generated full certificate had SHA-256

`512dcbd6de7a252e6bea5e1015c8c88507f7222140749ea19d6550a5e8e5aa7f`

and maximum relative symbol-determinant error

`9.27770225889e-61`.

## Scope firewall

A green workflow validates the exact mirrored script and the finite cases only. It does not formalize or prove:

- the Schur Cauchy identity;
- the infinite geometric moment determinant;
- the block Toeplitz integral theorem;
- a nonuniform-node perturbation theorem;
- any statement about zeta zeros, primes, or RH.

Five-alarm status: OFF.
