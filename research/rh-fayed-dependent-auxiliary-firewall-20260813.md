# RH claimed-proof firewall: the two auxiliary routes are dependent

Date: 2026-08-13

## Scope and provenance

This note audits H. A. Fayed, *A Simple Proof of the Riemann
Hypothesis*, arXiv:2209.01890v49 (3 August 2026), especially equations
(36), (43), (47), (49), and the subtraction in (54)--(55).

Primary source:

- https://arxiv.org/pdf/2209.01890

This is an obstruction to that claimed proof.  It is not a theorem about
the truth or falsity of RH.

## Claimant

Write
```
f(sigma) = zeta(sigma + i t)
g(sigma) = zeta(1 - sigma + i t)
a(sigma) = u^(1 - 2 sigma)
```
for fixed `u > 0`.  The paper's two auxiliaries are
```
I = f - a g
J = a^(-1) f - g.
```
The paper differentiates both routes at a simultaneous zero of `f` and
`g`, rescales one derivative, subtracts the two resulting expansions,
and interprets the displayed Bernoulli terms as forcing
`sigma = 1/2`.

## Critic: exact dependence

For every nonzero `a`,
```
a J = I,                 J = a^(-1) I.
```
Thus the two equations are one equation, not two.  If `b=a^(-1)` and
`J=b I`, the product rule gives
```
J' = b' I + b I'.
```
At a simultaneous zero, `I=0`, hence
```
a J' = I'.
```
The two derivative routes agree identically.  Their correctly rescaled
subtraction is exactly zero.

The accompanying Lean file proves these field identities and their
first-jet consequence without analytic assumptions.

## Smallest concrete calculus error

The source of the spurious survivor is visible in equations (43) and
(49).  These equations are announced as partial derivatives with
respect to `sigma`, but terms from powers of `u` are differentiated
with the `u`-derivative pattern.  For fixed `u > 0`,
```
d/dsigma [u^(-(s+k))]
  = -(log u) u^(-(s+k)),
```
whereas
```
d/du [u^(-(s+k))]
  = -(s+k) u^(-(s+k+1)).
```
The displayed terms such as
```
-(s+1) (2 sigma-1) B_2(u) / (2 u^(s+2))
```
have the second shape, although the paper is differentiating with
respect to `sigma`.  The missing `-log u` terms cancel the
`+log u` terms introduced when the zero equation is substituted into
the differentiated integral.  Retaining one side of that cancellation
creates the alleged leading term in (54).

This is also forced abstractly by `J=a^(-1)I`: any two correct
differentiations must obey the Lean-checked jet identity.  Therefore a
nonzero result after rescaling and subtracting certifies an error in the
calculus/remainder ledger.

## Rebuilder

What survives:

1. the Euler--Maclaurin/Perron representations may still be studied as
   identities for zeta;
2. the exact auxiliary dependence is a reusable audit check;
3. any repaired calculation must differentiate every `sigma`-dependent
   exponent with a `log u` factor and demonstrate exact cancellation.

What does not survive:

- the inference from (54)--(55) to `sigma=1/2`;
- the claimed RH proof.

## Formal scope

`RHFayedDependentAuxiliary.lean` proves only the exact algebraic
dependence and first-jet rescaling.  It does not formalize zeta, Perron
inversion, Euler--Maclaurin, or asymptotic remainders.  Those are
unnecessary to refute the claimed independence of the two routes, but
would be required for a full formal reconstruction of the paper.

Remaining assumptions for this obstruction: the paper's own definitions
of `I` and `J`, and ordinary field algebra.  Remaining assumptions for
RH: unchanged.
