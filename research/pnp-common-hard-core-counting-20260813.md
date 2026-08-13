# PNP common-hard-core counting theorem

Date: 2026-08-13
Base commit: `1c96c410f4cbccc397f2ec5ebba961e81275ddb8`.
Status: research theorem only; no NP-uniform construction and no P-vs-NP conclusion.

## Primary interfaces

Chen--Li--Yang, ECCC TR22-086 rev.1 (2022), https://eccc.weizmann.ac.il/report/2022/086/ gives the sparse-NP hardness-magnification frontier `2n+O(n/log log n)` and permits a one-sided lower-bound premise. Fan--Li--Yang, ECCC TR21-125 rev.1 (2021), https://eccc.weizmann.ac.il/report/2021/125/ is the source of the `2n-2` critical-path baseline. Internal circuit-count provenance is `verification/pnp-linear-random-list/verify.py` at commit `5a7335d5fb9ed65300abe45654b9fcb678f55195`.

Primary-source correction (2026-08-13): two different CLY parameter statements must not be conflated. Introductory Theorem 1.1 specializes to `ell=log^2 n/log log n` and states seed length `r=O(ell log^2 n)`. But the published proof of Theorem 4.1 explicitly invokes general Theorem 3.9 with `beta=2`, whose seed length is `O(ell log^(beta+1) n)=O(ell log^3 n)`. At `ell=Theta(log^2 n/log log n)`, the displayed Theorem-4.1 seed bound is therefore `O(log^5 n/log log n)`. The earlier version of this note incorrectly substituted the special Theorem-1.1 seed bound into Theorem 4.1. The companion note `research/pnp-hidden-seed-absorption-20260813.md` records the correction and a legal `beta=1` optimization lane separately.

## Theorem

Let `U_n={x in {0,1}^n: |x|=4}` and `Q=binom(n,4)`. For powers of two `n` sufficiently large, set `L=log_2 n` and `M=256 n L`. There exist disjoint `T_n,H_n subset U_n`, each of size `M`, such that every deterministic fan-in-two `B_2` circuit with at most `3n` gates that accepts all of `T_n` accepts at least `M/4` points of `H_n`.

For the false-positive error hypergraph of perfect-completeness deterministic support circuits, assign weight `4/M` to each point of `H_n` and zero elsewhere. Every edge then has weight at least one and total weight is exactly four. Hence `tau_f <= 4`.

Equivalently, for any distribution over those deterministic circuits, averaging over the fixed core `H_n` gives some `h in H_n` with false-positive probability at least `1/4`. Thus no one-sided probabilistic circuit supported on size-`3n` circuits has pointwise negative error below `1/4`.

## Proof

Draw ordered samples `T_1,...,T_M,H_1,...,H_M` independently and uniformly from `U_n`. Fix a circuit `C` and let `p` be its acceptance fraction on `U_n`. Call `C` bad if all `T_i` are accepted and fewer than `M/4` of the `H_i` are accepted.

If `p<=1/2`, then `Pr[C bad] <= p^M <= 2^{-M} <= exp(-M/16)`. If `p>1/2`, the number `X` of accepted `H_i` is `Bin(M,p)` with mean `mu>M/2`; `X<M/4` implies `X<=mu/2`, so the multiplicative Chernoff bound gives `Pr[C bad] <= exp(-mu/8) < exp(-M/16)`.

The elementary circuit overcount used in the base-branch regression is

`K(n,g) <= (g+1)(n+g+2)[16(n+g+2)^2]^g`.

For `g<=3n` in the finite regime it gives `log_2 K <= 10 n L`. Therefore

`K exp(-M/16) <= exp(((10 ln 2)-16)nL) < exp(-9nL)`.

The probability of any collision among the `2M` draws is at most `binom(2M,2)/Q < 2M^2/Q`. Using `Q>=n^4/192`, this is at most `25,165,824 L^2/n^2`, which is below `0.12` at powers of two `n>=2^18` and decreases thereafter. Hence the circuit-bad union bound plus collision bound is below one. A collision-free, no-bad-circuit outcome exists, and its underlying sets give the theorem.

## Claim + counterexample + salvage

**Claim (dead):** choosing one good finite pair per length yields the required sparse NP language.

**Counterexample:** finite existence gives no polynomial-time or NP-uniform membership predicate. An arbitrary choice sequence may be noncomputable; lexicographically choosing the first good pair still requires checking a universal condition over exponentially many circuits.

**Salvage:** the minimax/combinatorial target itself is solved nonuniformly. The remaining bridge is explicit NP-uniform selection of the pair.

## Selector-prefix preservation and sparsity firewall

For candidate slices `T_s subset {0,1}^m` indexed by `r` selector bits, pack `L_N={s||x:x in T_s}` with `N=m+r`. Restricting a size-`g` general DAG circuit to a fixed prefix never increases gate count. Thus

`g <= 2N+S` implies `g <= 2m+(S+2r)`.

So visible selection costs exactly `2r` relative to the `2m` baseline, and one-sided randomized completeness/error is preserved by restriction.

However, if all `2^r` selectors contribute at least one positive, then `|L_N|>=2^r`. The CLY sparse envelope `N^{log N/log log N}` has base-two logarithm only `Theta((log N)^2/log log N)`. Therefore an all-seed packed language can expose only `r=O((log N)^2/log log N)` selector bits. The tempting `r=Theta(N/log log N)` use of circuit slack violates sparsity exponentially.

For the hash family actually displayed in CLY Theorem 4.1, `beta=2` gives seed length `O(ell log^3 N)`; at `ell=Theta(log^2 N/log log N)` this is `O(log^5 N/log log N)`. Blindly exposing those seeds as positive prefixes exceeds the sparse-language exponent budget by a `Theta(log^3 N)` factor. The special introductory Theorem 1.1 has a shorter `O(ell log^2 N)` seed, but that is not the parameter choice written in the Theorem-4.1 proof.

**Salvage:** visible selectors are not the only class-preserving implementation. If all seed slices lie in a fixed sparse universe, one may hide the seed existentially in the NP witness without increasing input-space sparsity. The companion hidden-seed absorption theorem shows that the resulting hardness loss is governed by aggregate hard-core absorption, not by visible selector length or hard-core congestion.

## Barrier audit

The hard-core theorem is finite counting and relativizes. It neither invokes nor evades natural-proofs or algebrization barriers. It counts actual unrestricted fan-in-two Boolean DAG circuits, not formulas or algebraic surrogates. The average over the fixed core converts to a genuine pointwise error by finite averaging. The unresolved step is exactly finite/nonuniform to NP-uniform explicitness.

Recent Range Avoidance work remains relevant to that explicitization step, including Huang--Li--Zhong, ECCC TR25-049 rev.5 (2025), and Ren--Williams, ECCC TR26-118 rev.1 (2026), but no claim is made that those results place the needed selector in NP.

## Next target

Use the hidden-seed formulation rather than paying visible selector bits. Construct a polynomial-time verifiable anchor / admissible-seed relation whose positive union remains inside the fixed sparse universe and whose aggregate local-core absorption is `<1/4` (concretely `<=1/8` would give `tau_f<=8` from quarter-density local cores). Only if an unweighted common core is later required does one additionally need bounded multiplicity / `O(log log n)` congestion.
