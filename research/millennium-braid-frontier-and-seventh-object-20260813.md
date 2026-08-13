# Millennium braid frontier and the seventh object

Date: 2026-08-13 UTC

Status: **research synthesis; all six official problems remain open;
SIX-ALARM OFF.**

## 1. Outcome

The current bank does not contain a proof or disproof of RH, P versus NP,
BSD, Hodge, Navier--Stokes, or Yang--Mills.  It does contain four finite Lean
cores with a common clean hosted replay and several exact human theorems and
counterexamples that sharply reduce the live search space.

The common object exposed by the six lanes is a **marked cofinal residual
certificate**:

1. a finite or regulated object whose semantics are tied to the official
   target by an explicit mark;
2. a residual measuring everything omitted by the finite object;
3. a coercive, compactness, or decoding inequality converting residual size
   into target error;
4. one cofinal or universal schedule on which that error vanishes; and
5. a proved coverage map from the schedule to every object quantified by the
   official theorem.

Removing any one item reproduces a known dead path: an unmarked inverse limit
forgets Tamagawa orientation, a finite Schur solve has the wrong inequality
direction, a finite Fourier packet is not dynamically invariant, fixed
regulator estimates do not construct continuum Yang--Mills, and a formula or
partial-KW lower bound need not survive arbitrary DAG sharing.

This template is not itself a Millennium theorem.  Its value is diagnostic:
it identifies the first load-bearing arrow and makes that arrow falsifiable.

## 2. Clean finite kernel receipts

The exact four-source verifier is `stevemoraco/qs` PR #310.  Canonical replay
commit `bd56a51ba9df8effc45f41d1af3cc2c9e65dfd7f`, run/job
`31706185967/94467220976`, succeeded under Lean 4.32.1 and Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`.  All 36 requested axiom reports
use only `propext`, `Quot.sound`, and `Classical.choice`; no `sorryAx` occurs.
The durable receipt head `56ecb991664d0367240557cc81c3841d862de786`
received a second clean replay in run/job `31707539664/94471787302`.

| lane | exact finite core | kernel-output SHA-256 | formal boundary |
|---|---|---|---|
| RH | RH-Lean #992 head `5293b4f170a84db5aa7ff3a41167c3308842743e` | `0f28361ce6a36a1b0aad5af5f0c2618ca9da524ce79eda6bdbc7506f853bb2ab` | real-scalar Schur identity and residual bookkeeping only |
| Hodge | RH-Lean #928 head `31f5af6962198314c8d3afe5112ffdc4491d7495` | `668beec66131039858fb1919eb164a08edbcc720326d19d5da869b593c7eb31c` | finite coefficient recurrence only |
| Navier--Stokes | RH-Lean #976 head `9a0b837a6455df07e22a6a89b011a9bc1cb0150e` | `45fd1bfe133030ce199541b446e44b0fbad8f9573e30c2e0d87a1eb28c6befb6` | finite scalar octagon ledger/tangent obstruction only |
| Yang--Mills | RH-Lean #983 head `46455556507ee0878388c51ad6f048c3f6966674` | `e693c3d4999093cbb8f342619a743f36b49d730f1f81c87ff355b096c057fca8` | scalar consequences of assumed spectral budgets only |

These receipts verify exactly what the source files say.  They do not verify
the human analytic, geometric, arithmetic, or continuum bridges named below.

## 3. Six-lane frontier

### 3.1 RH

**Claimant.**  The odd-Weil/Feshbach route has the exact safe correction

```text
Fhat_y - F = <r,D^{-1}r> <= ||r||^2/mu,
r = Dy-Bx,  D >= mu I.
```

The verified scalar shadow is

```text
A-B^2/D = (A-2By+Dy^2) - (Dy-B)^2/D.
```

**Critic.**  Dropping the residual is false already for
`A=1`, `B=sqrt(1+epsilon)`, `D=1`, `y=0`: the completed square is `1` while
the exact Schur value is `-epsilon`.

**Rebuilder.**  Construct one fully normalized cofinal schedule with complete
prime, prime-power, archimedean, endpoint, and high-tail terms and certify

```text
Delta_n = max(0,-lambda_min(Fhat_n))
        + ||D_n Y_n-B_n||_op^2/mu_n  -> 0.
```

This is the current highest-EV falsifiable RH ticket.  A fixed-support or
finite-cutoff table has no cofinal force.

**Execution firewall.**  The current odd-Weil branch does not yet expose a
source-complete formula or program mapping the localized odd basis to the
numerical blocks `A_n,B_n,D_n`; nor does it provide a constructive Yoshida
cutoff or a computable coercivity constant.  Therefore even the first honest
interval experiment for `Delta_n` begins one bridge earlier: specify and
validate the complete Weil matrix, including prime powers, archimedean and
endpoint normalization, and prove a quantitative cutoff/complement bound.
The Connes/prolate lane has stronger numerical motivation but the same missing
proof-grade continuum/complement certificate, together with strip-amplified
approximation error.  It does not presently outrank this ticket.

For a bounded Connes feasibility probe, the first honest target is one
prime-active cutoff with an endpoint-zero even/odd basis (initially `N=8`),
outward-rounded matrix and tail assembly, interval eigenvalue counts and
candidate residual.  It must additionally certify the continuum complement
floor `d0` and cross-coupling bound `beta`; otherwise a hidden state outside
the Galerkin space can reverse the result.  The decisive finite-to-continuum
test is

```text
min(b1,d0)-b0 > 2 beta
```

plus the required odd/even ordering.  Current executable Connes artifacts use
synthetic rational spectra rather than actual Weil matrices, so they do not
instantiate this test.

### 3.2 P versus NP

**Claimant.**  The strongest exact cut in the current bank is the fixed
Quarter-Approx-MCSP promise.  A general-circuit lower bound exceeding
`N (log N)^(logStar N)` infinitely often would imply
`NP` is not contained in `P/poly`, hence `P != NP`.

**Critic.**  Plain partial-KW node lower bounds cannot reach that target:
a coordinate hitting set of size `h` yields a shared DAG of size at most
`4h-3`, and the quarter moat gives a linear universal ceiling.  Pairwise
distance, support, entropy, rectangle covers, and formula-leaf counts do not
price arbitrary shared computation.

**Rebuilder.**  Find a measure that charges global range membership or
inversion under arbitrary circuit DAG sharing.  The mark is the fixed
universal consistency language; the residual is the gap between local
separation data and a global shared evaluator.  No such lower bound is known.

### 3.3 BSD

**Claimant.**  Deep same-parity Mazur--Tate layers can recover signed Selmer
lambda-invariants exactly under the proved hypotheses, and zero signed
mu/lambda can force exact signed Selmer vanishing.  This is banked in RH #219,
with finite companion RH-Lean #999 and public qs #321 replay.

**Critic.**  This does not recover the base Mordell--Weil rank, regulator,
Tamagawa factors, Sha order, or complex leading coefficient.  More generally,
the inverse limits of all towers `Z/p^(n+a)` are isomorphic to `Z_p`; an
unmarked limit forgets `a = ord_p c_p(E)`.  Unit changes can preserve
cohomology/Fitting/Smith data while changing a based determinant.

**Rebuilder.**  Construct a marked Neron control complex whose specialization
retains the level-zero lattice `p^a Z_p`, is compatible with the Kato zeta
element and Poitou--Tate determinant orientation, and neither loses nor
double-counts the local Tamagawa/Euler factor.  The smallest hostile test is a
one-step split-Tate specialization with exact sign and index.

### 3.4 Hodge

**Claimant.**  For `Y=B x P^m`, `m=N-2q`, the alternating primitive suspension
is an exact polarized Hodge-structure isomorphism

```text
Sigma_L : P^(2q)(B,Q)(-m) ~= P^D(Y,Q),
rho_* Sigma_L = id,
Q_Y(Sigma theta,Sigma eta) = (m+1) Q_B(theta,eta).
```

Algebraicity transfers in both directions because `Sigma_L` uses algebraic
Lefschetz/projective classes and the inverse is proper pushforward.

**Critic.**  This is exact cohomological repackaging, not cycle construction.
The endpoint-only term is not primitive: for `B=P^2`, `q=0`, `m=2`, the
unique primitive combination is `h^2-Lh+L^2`, not `h^2`.

**Rebuilder.**  The live bridge is a bounded-Chow-complexity specialization
theorem strong enough to lift dense good-reduction cycles with one
denominator and uniformly bounded positive/negative degree.  Proving the
required uniform bound is presently Hodge-sized.

### 3.5 Navier--Stokes

**Claimant.**  The explicit eight-mode noncollinear vertical octagon lies in
the exact high--auxiliary cancellation kernel and leaves only the desired
projected high--high transfer.  The full finite-support kernel is generated by
polynomials in `x-x^-1+y-y^-1`.

**Critic.**  The retained Euler transfer is transverse to that kernel, and
positive viscosity gives incompatible tangent equations.  Thus the octagon is
an instantaneous stress synthesizer, not an invariant PDE mechanism.  The
collinear alternative has only the infinite profile `C/n`, which lies in
`H^s` exactly for `s<1/2`; finite truncations leave a terminal defect of fixed
size.

**Rebuilder.**  Any viable closure must be infinite or approximate and must
include a dynamically replenished interaction graph plus a quantitative
shadowing theorem through the critical norm.  Finite exact invariant Euler
closures remain blocked by finite-mode rigidity.

### 3.6 Yang--Mills

**Claimant.**  In the pure-electric compact-group model, every centered
physical observable has a spectral defect floor, and a simple Wilson
character has the exact defect

```text
1-exp(-g_a^2 L C_2(R)/2).
```

For an interacting Hamiltonian with an admissible positive gauge-invariant
ground state, the exact ground-state transform reduces the trial-state ticket
to

```text
Rayleigh(F Omega)
  = g_a^2/(2a) * Dirichlet_mu(F)/Var_mu(F).
```

**Critic.**  If `g_a^2/a -> infinity`, the pure-electric gap floor forbids an
`O(a)` transfer defect for every nonzero centered gauge-invariant observable.
A fixed physical Wilson loop is worse: its defect tends to one.  Vacuum
contamination `1+epsilon W` also shows why centering is essential.

**Rebuilder.**  For one explicit flowed magnetic/action-density multiplication
packet at fixed physical radius, prove a variance floor and the
observable-specific reverse-Poincare estimate

```text
Dirichlet_mu(F)/Var_mu(F) = O(a/g_a^2)
```

on the same Osterwalder--Schrader continuum trajectory.  Fixed-lattice or
pure-electric estimates cannot cross this bridge.

## 4. Allocation

The immediate computation-first order is:

1. RH: first make one complete normalized Weil matrix and complement bound
   executable; then attempt a small interval residual-penalized schedule and
   falsify it early if the defect plateaus;
2. P versus NP: seek a DAG-sharing-sensitive global inversion measure, not
   another local separation statistic;
3. BSD: test the marked split-Tate control specialization for sign and factor
   duplication;
4. Navier--Stokes: search infinite/approximate replenishing graphs with a
   critical-norm error budget;
5. Yang--Mills: isolate a multiplication observable for the interacting
   reverse-Poincare ticket;
6. Hodge: allocate only to an actual uniform Chow-complexity bound or a
   counterexample to the proposed specialization hypotheses.

The ranking is a research allocation, not a probability theorem.  It should
change immediately when a complete residual experiment or hostile example
invalidates one of its premises.

## 5. Bell status

No official theorem has a complete human proof and end-to-end Lean
formalization.  The four clean kernel receipts are deliberately narrower
finite firewalls.  Every remaining finite-to-infinite, local-to-global,
cohomological-to-algebraic, fixed-regulator-to-continuum, and one-sector-to-
full-target arrow named above remains a theorem obligation.

**SIX-ALARM: OFF.  RESEARCH BANKED.**
