# Ri 2026: no nonnegative multiplicity correction preserves both critical coercivity and uniform averaging

**Date:** 2026-08-13  
**Primary source:** Myong-Hwan Ri, arXiv:2601.15685v1.  
**Scope:** strongest salvage audit of the threshold-superposition mechanism; not a Navier–Stokes theorem.

## 1. Why reweighting is the natural proposed repair

The fatal error in (3.12) omits the multiplicity of the map

\[
k\longmapsto j_0(2k)=\lceil\log_2k\rceil+2.
\]

A natural response is to multiply the `k`-th high-frequency energy inequality by a nonnegative correction `q_k`, reducing the contribution of large exceptional fibers.

The corrected superposition would be

\[
\mathcal E_{s,q}(u)
=
\sum_{k\ge1}q_k k^s\|u^k\|_2^2.
\]

Because

\[
\|u^k\|_2^2
=
\sum_{n\ge k}\|u_{n,n+1}\|_2^2,
\]

Tonelli's theorem gives the exact identity

\[
\mathcal E_{s,q}(u)
=
\sum_{n\ge1}W_{s,q}(n)\|u_{n,n+1}\|_2^2,
\qquad
W_{s,q}(n):=\sum_{k=1}^n q_k k^s.
\tag{1}
\]

Thus equivalence with the source's target Sobolev norm requires constants

\[
0<c_-\le c_+<\infty
\]

such that

\[
c_-n^{s+1}\le W_{s,q}(n)\le c_+n^{s+1}
\qquad(n\ge1).
\tag{2}
\]

This necessity is exact: test (1) on a field supported in one Fourier annulus `n<|xi|<n+1`.

The nonlinear estimate, after the same reweighting, requires a uniform constant `C` with

\[
V_{s,q}(n)
:=
\sum_{k=1}^nq_kk^s b(j_0(2k))
\le Cn^{s+1}.
\tag{3}
\]

We prove that no nonnegative sequence `q_k` can satisfy both (2) and (3) for the source's sparse weights.

## 2. A long block of large coefficients

Let

\[
m_r=2^{2^r}.
\]

For every shell index

\[
m_r-r\le j\le m_r+r,
\]

the source definition gives

\[
a(j)=\log_2j.
\]

The last term of the exponentially weighted average

\[
b(j)=2^{-j-1}\sum_{i=1}^j2^ia(i)
\]

gives

\[
b(j)\ge\frac12a(j)=\frac12\log_2j.
\tag{4}
\]

For all sufficiently large `r`, `m_r-r>=m_r/2`; hence throughout this whole block

\[
b(j)\ge B_r:=\frac{2^r-1}{2},
\qquad
B_r\longrightarrow\infty.
\tag{5}
\]

The fibers of `j_0(2k)` are dyadic:

\[
j_0(2k)=j
\quad\Longleftrightarrow\quad
2^{j-3}<k\le2^{j-2}.
\tag{6}
\]

Consequently all thresholds in the long interval

\[
2^{m_r-r-3}<k\le2^{m_r+r-2}
\tag{7}
\]

carry coefficient at least `B_r`.

Put

\[
N_r=2^{m_r+r-2},
\qquad
L_r=2^{m_r-r-3}.
\]

Then

\[
\frac{L_r}{N_r}=2^{-2r-1}.
\tag{8}
\]

The high-coefficient region therefore contains all but an exponentially tiny initial fraction of the prefix ending at `N_r`.

## 3. Critical coercivity forces mass into the spike block

By the upper half of (2),

\[
W_{s,q}(L_r)
\le
c_+L_r^{s+1}
=
c_+2^{-(2r+1)(s+1)}N_r^{s+1}.
\]

For sufficiently large `r`, this is at most

\[
\frac{c_-}{2}N_r^{s+1}.
\tag{9}
\]

By the lower half of (2),

\[
W_{s,q}(N_r)\ge c_-N_r^{s+1}.
\tag{10}
\]

Subtracting (9) from (10), and using `q_k>=0`, gives

\[
\sum_{L_r<k\le N_r}q_kk^s
\ge
\frac{c_-}{2}N_r^{s+1}.
\tag{11}
\]

Thus any nonnegative superposition equivalent to the critical Sobolev norm must place a fixed fraction of its prefix mass inside the long exceptional block.

## 4. Uniform nonlinear averaging becomes impossible

Every threshold in (11) has `b(j_0(2k))>=B_r`. Therefore

\[
\begin{aligned}
V_{s,q}(N_r)
&\ge
B_r\sum_{L_r<k\le N_r}q_kk^s\\
&\ge
\frac{B_rc_-}{2}N_r^{s+1}.
\end{aligned}
\tag{12}
\]

Since `B_r->infinity`, (12) contradicts the uniform upper bound (3).

Hence:

\[
\boxed{
\begin{gathered}
\text{No nonnegative threshold reweighting can simultaneously}\
\text{preserve equivalence with the critical Sobolev superposition}\
\text{and uniformly average Ri's unbounded sparse coefficients.}
\end{gathered}}
\]

This is stronger than the single-fiber counterexample. It rules out every positive multiplicity correction that stays within the printed energy-superposition architecture.

## 5. Why reciprocal-fiber normalization visibly loses a half derivative

The most direct correction assigns approximately one unit of total weight to each dyadic fiber, so

\[
q_k\asymp k^{-1}.
\]

Then

\[
W_{s,q}(n)\asymp\sum_{k\le n}k^{s-1}.
\]

For `s>0` this grows like `n^s`, rather than `n^{s+1}`. For `s=0` it grows only logarithmically. Through (1), this controls the Sobolev order `s/2`, not `(s+1)/2`.

Thus the naive multiplicity normalization loses exactly one power of frequency in the squared norm, equivalently one half derivative.

## 6. Claimant / critic / rebuilder

### Claimant

Insert nonnegative correction weights to pay for the omitted fiber multiplicities while retaining the same superposed energy norm.

### Critic

The sparse windows are long in shell index. They occupy an arbitrarily large multiplicative range of integer thresholds, and every coefficient in that range diverges with `r`. Critical norm equivalence forces substantial positive mass into the range, making the nonlinear average diverge.

### Rebuilder

A repair must leave the current positive threshold-superposition framework. Possible new architectures are:

1. a cancellation-bearing signed or matrix-valued superposition with a separately proved coercive lower bound;
2. a different supercritical space whose rescaling smallness does not require unbounded weights on long consecutive shell windows;
3. an equation-specific nonlinear cancellation that removes `b(j_0(k))` before superposition;
4. an entirely different regularity mechanism.

Signed weights cannot be introduced casually: the left-hand energy and dissipation would no longer be manifestly nonnegative. Every coercivity and limit passage would need a new theorem.

## 7. Lean firewall

The abstract finite core is theorem

`NavierStokesRiExceptionalFiberFirewall.longSpikeBlockReweightingNoGo`.

It proves that if old corrected mass is at most half the mass required by critical coercivity, the spike block must carry the other half; an unbounded positive spike coefficient then contradicts a uniform nonlinear budget.

The companion theorem

`criticalFiberRetentionAndSpikeAverageIncompatible`

covers the one-fiber version.

The Lean theorem does not formalize Fourier tails, Tonelli, Sobolev spaces, or the source-specific construction of the long block. Those analytic identifications are supplied explicitly above.

## Status

The strongest natural repair of Ri's printed proof is obstructed. This does not prove or disprove the official Navier–Stokes theorem. SIX-ALARM remains off.
