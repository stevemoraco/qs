# P versus NP: finite-cutoff and shared-DAG firewall

Date: 2026-08-13

**Status:** durable obstruction only. This is **not** a proof that `P != NP`.

## Exact official target

Stephen Cook's official Clay formulation defines `NP` by polynomially bounded
witnesses checked by a polynomial-time relation and asks exactly: **Does
`P = NP`?** SAT is the canonical NP-complete endpoint. A lower-bound route
must therefore produce an explicit language in `NP \ P`, or a theorem already
proved to imply that separation with all uniformity and asymptotic quantifiers
preserved.

Primary source: Stephen Cook, “The P versus NP Problem,” in *The Millennium
Prize Problems*, problem statement pp. 88–89 and SAT reduction pp. 92–93:
https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf

## Kernel-checked countermodel

For arbitrary finite cutoff `N` and degree `k`, define

```
C(N,k,n) = n^k + 1   if n <= N,
           0         if n > N.
```

Lean proves both:

1. every checked input satisfies `n^k < C(N,k,n)` for `n <= N`;
2. after the cutoff, `C(N,k,n)=0`, so it is eventually bounded by zero.

Thus no finite collection of exact circuit-size values, exhaustive searches,
SAT certificates, signature ranks, or numerical gaps entails a superpolynomial
asymptotic lower bound without an independently proved induction, monotonicity,
extension, or structural theorem.

## Shared-DAG critic

The existing bank correctly formalizes an abstract diamond-chain recurrence:
unfolding a depth-`d` shared DAG can require `2^d` tree copies while the DAG
has only linear excess. That is a real formula-versus-circuit warning, but it is
an upper bound on a particular unfolding procedure, not a Boolean circuit lower
bound. A different circuit may exploit sharing or compute the same function by
another representation. Counting unfolded trees therefore cannot be charged
to minimum unrestricted circuit size without a semantic invariant subadditive
under every allowed gate and sharing operation.

Existing Lean recurrence:
https://github.com/stevemoraco/qs/blob/777651ee920a32f021165b778e753bfeaab52dfb/verification/pnp-dag-unfolding/PNPDAGUnfoldingFinite.lean

## Claim / counterexample / salvage

| Claim | Smallest counterexample | Best salvage |
|---|---|---|
| Finite verification through `N` proves an asymptotic lower bound. | `C(N,k,n)` beats `n^k` on every checked `n` and is zero thereafter. | Use computation only to falsify candidates or verify the finite base of a separately proved extension theorem. |
| Exponential DAG unfolding proves exponential circuit size. | A depth-`d` diamond DAG has linear shared size and exponential naive tree expansion. | Seek a semantic potential subadditive under all gates and stable under fanout/reuse. |
| Counting many local signatures forces many circuit gates. | One shared subcircuit can feed arbitrarily many output contexts; occurrence counts need not be additive. | Prove a bounded-reuse/direct-sum lemma for the exact circuit model, or state the restriction. |
| `forall k, exists L` hard implies `exists L, forall k` hard. | `R(k,L) := L <= k`: every `k` misses `L=k+1`, but every `L` obeys `k=L`. | Preserve one uniformly defined NP language across all exponents. |

The quantifier countermodel is already Lean-checked at:
https://github.com/stevemoraco/qs/blob/1b32255c64409887960ff0f0fd1ac5a1ff391e89/verification/round218-pnp-cly-quantifier/PNPCLYQuantifierFirewallFinite.lean

## Smallest live target

Formalize unrestricted Boolean-circuit semantics and a semantic potential
`Phi` with kernel-checked laws: small on inputs; bounded increase per gate;
no duplicated charge under reuse; and a superpolynomial value on one explicit,
uniform NP language. The latter two laws are the missing lower-bound bridge.

## Verdict

- **SURVIVES:** finite computation for falsification and finite theorem bases;
  shared-DAG unfolding as a formula/circuit warning.
- **DIES:** a silent finite-range, unfolding-size, or signature-count inference
  to an unrestricted asymptotic circuit lower bound.
- **BEST SALVAGE:** demand an exact semantic resource theorem before further
  large computation.
- **CLAY STATUS:** unresolved; no alarm.
