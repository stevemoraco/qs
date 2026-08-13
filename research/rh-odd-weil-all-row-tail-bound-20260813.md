# RH localized odd-Weil all-row tail bound

Date: 2026-08-13 UTC

Status: **human theorem, independently normalization-audited;
not Lean-formalized; no RH conclusion; SIX-ALARM OFF.**

## 1. Statement

Fix `a>0` and put

```text
s_j(t) = a^(-1/2) sin(pi j t/a) 1_{|t|<=a},
H_jl(a) = Q_W^a(s_j,s_l),                         j,l>=1.
```

Here `Q_W^a` is Suzuki's closed localized Weil form, restricted here to
`H_0^1(-a,a)`.
The conventional notation `W(s_j*~s_l)` below means this closed extension,
not an unsupported application of the original test-function distribution.

Let `gamma0` be Euler's constant, `psi` the digamma function, and `Phi` the
Hurwitz--Lerch function.  Define the finite prime-power sums

```text
S(a) = sum_{2<=n<=exp(2a)} Lambda(n)/sqrt(n),
T(a) = sum_{2<=n<=exp(2a)} Lambda(n)/sqrt(n) (2a-log n),
```

and the explicit endpoint-variation majorant

```text
V(a) = 4(exp(a)+exp(-a)-2)
     + T(a)
     + a abs(psi(1/4)-log pi)
     + (C-exp(-a) Phi(exp(-4a),2,1/4))/4,

C = Phi(1,2,1/4) = pi^2+8 Catalan.
```

For `l>=1`, set

```text
K_l(a) = 2 V(a)
       + 2 pi a l
       + 2 a (abs(log a)+1-log 2)
       + (4a/pi) (log(2pi)+gamma0+2 S(a)+8 sinh(a)+a).
```

Then the following all-row bound holds:

```text
|H_jl(a)| <= l K_l(a)/(a j),                    j,l>=1.       (1)
```

Consequently, for any finite family of scalar coefficients `c_1,...,c_M`,

```text
(sum_{j>M} |sum_{l=1}^M H_jl(a)c_l|^2)^(1/2)
  <= (1/(a sqrt(M))) sum_{l=1}^M l K_l(a)|c_l|.              (2)
```

The same estimate holds for row-vector coefficients `C_l` with Euclidean
norms on the right.  In particular, for integers `0<=N<M` and the residual
matrix

```text
R_j = sum_{N<l<=M} H_jl Y_l - (H_j1,...,H_jN),   j>M,
```

we have the fully explicit operator-tail estimate

```text
||(R_j)_{j>M}||_op <= ||(R_j)_{j>M}||_F
 <= [sum_{k=1}^N k K_k(a)
       + sum_{l=N+1}^M l K_l(a) ||Y_l||_2] /(a sqrt(M)).      (3)
```

This is deliberately coarse.  It is nevertheless an actual bound on **all**
omitted rows, not a finite residual surrogate.

## 2. Exact reduction

Suzuki 2026, (1.8) and Lemma 3.1, identify the closed form on
`H_0^1(-a,a)`.  Polarization gives, for `v,w` in that space,

```text
Q_W^a(v,w)=<G_a Dv,Dw>,
D=i d/dt,   G_a=P_a G P_a.
```

This is the required domain statement for the zero-extended sine modes; no
unsupported application of a test-function distribution is being made.
For those modes,

```text
D s_j=i(pi j/a^(3/2))c_j,
integral_{-a}^a c_j(t)dt=0.
```

Thus the right projection fixes `D s_j`, and self-adjointness of `P_a`
removes the left projection against `D s_l`.  The factors `i` and
`conj(i)` contribute `+1`.  Since Suzuki's screw kernel is `g=-Psi`, this
fixes both the coefficient and the global minus sign in the formula below.

Write

```text
c_l(u)=cos(pi l u/a) 1_{|u|<=a},
F_l(t)=integral_{-a}^a Psi(t-u) cos(pi l u/a) du,
alpha_j=pi j/a.
```

The normalized screw-kernel identity gives, using symmetry to place `l` in
the inner integral,

```text
H_jl(a)=-(pi^2 j l/a^3) integral_{-a}^a F_l(t) cos(alpha_j t) dt.  (4)
```

Here `Psi=-g` in Suzuki's notation.  The only analytic issue is whether two
integrations by parts in (4) are legitimate.  They are: `F_l''` is an
ordinary `L1(-a,a)` function, despite the prime-power kinks and the finite-part
singularity described next.

## 3. The distributional second derivative

Suzuki's distributional formula is

```text
Psi'' = -1/2 Pf(1/abs(t))
        -(2A+1) delta_0
        -sum_{n>=2} Lambda(n)/sqrt(n)
             (delta_(log n)+delta_(-log n))
        -r'',

A=(log(2pi)+gamma0-1)/2,
2A+1=log(2pi)+gamma0.                              (5)
```

For `|x|<a`, convolution of the finite-part term with `c_l` is the locally
integrable function

```text
P_l(x) = integral_{-a}^a
           [cos(pi l u/a)-cos(pi l x/a)]/abs(x-u) du
         + cos(pi l x/a) log(a^2-x^2).                       (6)
```

Here is the finite-part limit, including its endpoint control.  Suzuki's
normalization is

```text
<Pf(1/abs(t)),f>
 = limit_{epsilon->0+}
     [integral_{|t|>epsilon} f(t)/abs(t) dt
        +2 log(epsilon) f(0)].
```

Let `c=c_l`, `L=pi l/a`, and, for `0<epsilon<a`, set

```text
P_epsilon(x)
 = integral_{[-a,a], |u-x|>epsilon} c(u)/abs(x-u) du
     +2 log(epsilon)c(x).
```

If both endpoint distances `a+x` and `a-x` exceed `epsilon`, split
`c(u)=c(x)+(c(u)-c(x))` and use

```text
integral_{[-a,a], |u-x|>epsilon} du/abs(x-u)
 = log((a+x)(a-x))-2 log(epsilon).
```

Letting `epsilon` tend to zero gives (6).  In either endpoint strip the only
additional term is `c(x)log(epsilon/d)`, where `0<d<=epsilon` is the
truncated endpoint distance.  The Lipschitz bound
`|c(u)-c(x)|<=L|u-x|` therefore yields

```text
||P_epsilon-P_l||_1
 <= 4aL epsilon + 2 integral_0^epsilon log(epsilon/d) dd
 = (4 pi l+2)epsilon -> 0.                                  (6a)
```

Fubini against a smooth compactly supported test function identifies this
`L1` limit with `Pf(1/abs(t))*c_l` as a distribution.  In particular, (6)
also handles the jumps introduced by zero-extending the cosine at the two
endpoints.

Thus

```text
F_l''(x) = -P_l(x)/2
           -(log(2pi)+gamma0)c_l(x)
           -sum_{n<=exp(2a)} Lambda(n)/sqrt(n)
              [c_l(x-log n)+c_l(x+log n)]
           -integral_{-a}^a r''(x-u)c_l(u)du.                (7)
```

Formula (7) records the kink regularity exactly.  Each prime-power delta in
`Psi''` becomes a compactly supported shifted cosine, possibly with jump
discontinuities where its shifted support enters or leaves `[-a,a]`; it does
not remain a delta.  The finite-part term has only the integrable endpoint
logarithm in (6).

It follows from (6a), the finite shifted-cosine sum, and Young's inequality
for the remainder that `F_l''` belongs to `L1(-a,a)` distributionally.
Since `F_l` is continuous, the one-dimensional distribution theorem gives
`F_l in W^(2,1)(-a,a)`.  The weak integrations by parts and their endpoint
traces below are therefore legitimate.

The regular remainder in (5) has the exact pointwise expression, for `t>0`,

```text
r''(t) = -2 cosh(t/2)
         + e^(-t/2)/(1-e^(-2t)) - 1/(2t),                    (8)
```

with its continuous value at zero.  If

```text
h(t)=e^(-t/2)/(1-e^(-2t))-1/(2t)
    =(1/2)(e^(t/2)/sinh(t)-1/t),
```

then

```text
|h(t)| <= 1/4,                                               (9)
```

and hence

```text
integral_{-2a}^{2a}|r''(t)|dt <= 8 sinh(a)+a.                (10)
```

For completeness, the upper inequality in (9) is equivalent to

```text
(2+t)sinh(t)-2t e^(t/2) >= 0.
```

Its power-series coefficient of `t^n` is zero for `n=1,2`, is
`[2/n-2^(2-n)]/(n-1)! >=0` for odd `n>=3`, and is
`[1-2^(2-n)]/(n-1)! >=0` for even `n>=4`.  For the lower inequality,
`t>=2` is immediate.  On `0<=t<=2`, convexity puts both `e^(t/2)` and
`e^(-3t/2)` below their endpoint chords, giving

```text
e^(t/2)+e^(-3t/2) <= 2+t,
```

because `(e+e^(-3)-2)/2<1`.  Therefore
`d/dt[t e^(t/2)-sinh(t)]>=0`, so `h(t)>=0` on this interval.
The displayed strict inequality follows already from the elementary bounds
`e<3` and `e^(-3)<1`.

## 4. Explicit `L1` estimates

The Lipschitz bound for cosine and (6) give

```text
||P_l||_1 <= 4 pi a l + L(a),
L(a) = integral_{-a}^a |log(a^2-x^2)|dx
     <= 4a(abs(log a)+1-log 2).                              (11)
```

Indeed, the difference quotient in (6) is at most `pi l/a` pointwise,
and

```text
integral_{-1}^1 -log(1-y^2)dy = 4(1-log 2).
```

Also

```text
||c_l||_1 = 4a/pi.                                          (12)
```

Every shifted prime term in (7) has `L1(-a,a)` norm at most `4a/pi`.
Young's inequality and (10) give

```text
||r''*c_l||_{L1(-a,a)} <= (4a/pi)(8 sinh(a)+a).              (13)
```

Finally, `F_l` is even and

```text
|F_l'(a)|
 <= integral_0^{2a}|Psi'(t)|dt
 <= V(a).                                                    (14)
```

To check the last displayed constant without hiding a tail, away from the
finitely many points `t=log n`, direct differentiation of Suzuki's formula is

```text
Psi'(t)=2(e^(t/2)-e^(-t/2))
        -sum_{n<=e^t} Lambda(n)/sqrt(n)
        +(psi(1/4)-log pi)/2
        +(1/2)e^(-t/2) Phi(e^(-2t),1,1/4).                  (15)
```

Triangle integration of (15) on `[0,2a]` is exactly the stated `V(a)`:
the prime step function integrates to `T(a)`, and the last term integrates
to

```text
[C-e^(-a)Phi(e^(-4a),2,1/4)]/4.
```

Equations (7), (10)--(14) imply

```text
2|F_l'(a)|+||F_l''||_1 <= K_l(a).                            (16)
```

In particular `F_l` belongs to `W^(2,1)(-a,a)`, which justifies the two weak
integrations by parts.

## 5. Two integrations by parts and the tail

Because `sin(alpha_j a)=sin(-alpha_j a)=0`,

```text
integral_{-a}^a F_l(t)cos(alpha_j t)dt
 = [F_l'(t)cos(alpha_j t)]_{-a}^a/alpha_j^2
   - integral_{-a}^a F_l''(t)cos(alpha_j t)dt/alpha_j^2.
```

Evenness gives `F_l'(-a)=-F_l'(a)`.  Combining this identity with (4) and
(16) proves (1).  Then

```text
sum_{j>M} 1/j^2 <= integral_M^infinity dx/x^2 = 1/M
```

proves (2), and the rowwise triangle inequality followed by
`||.||_op<=||.||_F` proves (3).

## 6. Uniformity and sharpness

For a compact regulator interval `0<a_minus<=a<=a_plus`, (1)--(3) are uniform
after replacing `1/a` by `1/a_minus`, every monotone term by its value at
`a_plus`, and `abs(log a)` by
`max(abs(log a_minus),abs(log a_plus))`.  This proof does **not** assert a
uniform constant on `(0,a_plus]`; the displayed coarse majorant after the
external `1/a` factor, equivalently `K_l(a)/a`, can diverge at zero and that
endpoint requires a separate scaled analysis.

The `1/j` column rate should not be silently improved.  Since `F_l''` is in
`L1`, Riemann--Lebesgue gives the exact leading alternative

```text
H_jl(a) = -2(-1)^j l F_l'(a)/(a j) + o(1/j).                 (17)
```

Here `j` tends to infinity with `a,l` fixed.

Thus a nonzero endpoint trace `F_l'(a)` produces a harmonic, not absolutely
summable, column tail.  It is nevertheless square summable, which is exactly
what the residual certificate needs.  Any proposed `O(1/j^(1+epsilon))`
bound must first prove the additional cancellation `F_l'(a)=0` (and further
regularity); it does not follow from parity or from the prime-power kinks.

The smallest smooth-kernel check already exposes the omitted endpoint term:
replace `Psi(t)` by the even kernel `t^4`.  Then

```text
F_l'(a)=integral_{-a}^a 4(a-u)^3 cos(pi l u/a)du
       =48 a^4 (-1)^l/(pi^2 l^2),
```

which is nonzero.  Thus a proof that simply deletes the boundary trace after
the second integration by parts is false even before arithmetic kinks enter.

## 7. Claimant, critic, rebuilder

**Claimant.**  Equations (1)--(3) close the previously missing infinite-row
residual estimate for every fixed `(a,N,M,Y)` with elementary,
outward-computable constants.

**Critic.**  The bound grows rapidly with `a`, uses a crude triangle estimate,
and does not supply Suzuki's separate high-block floor `mu_L`.  More
decisively, `K_l(a)=2 pi a l+O_a(1)`, so the right side of (3) need not tend
to zero along a cofinal sequence without a weighted decay theorem for the
rows `Y_l`.  It therefore does not by itself produce a Schur certificate or
an RH result.  Dropping the boundary trace in the second integration by parts
would falsely predict a faster tail; (17) isolates the exact obstruction.

**Rebuilder.**  Replace the triangle bounds by interval evaluation of the
exact quantities `2|F_l'(a)|+||F_l''||_1`.  Combine (3) with the separately
effectivized high-block coercivity bound, and prove enough weighted decay of
the computed rows `Y_l` to force the full residual to zero.  Only then may
the result enter the residual-squared Schur core cofinally.

## 8. Primary sources

- Masatoshi Suzuki, *Aspects of the screw function corresponding to the
  Riemann zeta-function*, arXiv:2206.03682v4, especially (1.1), (3.8), and
  Sections 3.4--3.5:
  https://arxiv.org/html/2206.03682v4
- Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1, especially (1.3)--(1.8), (2.2), (2.9)--(2.11), and
  Lemma 3.1:
  https://arxiv.org/html/2606.09096v1

No finite-to-infinite positivity, cofinal, or RH arrow is claimed here.

## 9. Hostile audit ledger

The following distinctions are part of the theorem statement, not editorial
fine print.

1. **Finite-part convolution.**  Formula (6) is the standard Hadamard
   finite-part action with Suzuki's normalization, and its displayed
   symmetrized form has the correct quadratic-form sign.  The epsilon
   deletion and `2 log epsilon` subtraction are written out above, and (6a)
   proves convergence in `L1`, including the endpoint strips.  Thus the
   finite-part normalization is closed rather than imported by analogy.

2. **Form-domain extension.**  The compactly supported smooth identity
   `Q_W(v,w)=integral integral g(x-y)v'(y)conj(w'(x))` is primary-source
   exact.  The sine functions are in `H_0^1(-a,a)` but their zero extensions
   are not `C_c^infinity`.  Suzuki 2026 (1.8) and Lemma 3.1 state the closed
   `H_0^1` form identity through `B_a=D*G_aD`; polarization gives the mixed
   identity used in Section 2.  This closes the domain extension without
   requiring a bespoke sine approximation sequence.

3. **Regular archimedean remainder.**  Equation (8) follows algebraically
   from Suzuki 2026's decomposition
   `r=r_0+r_1`, with `r_0''=-2 cosh(t/2)` and
   `r_1''=e^(-|t|/2)/(1-e^(-2|t|))-1/(2|t|)`.  The apparent singularity is
   removable.  The proof of `|h|<=1/4` is included above.  No unproved special
   function tail remains in (10).

4. **Prime deltas.**  For
   `q_tau(t)=w(|t|-tau)_+`, the distributional identity is
   `q_tau''=w(delta_tau+delta_-tau)`.  Since Suzuki's `g` contains the prime
   hinge with a plus sign and `Psi=-g`, the coefficients in (5) are
   `-Lambda(n)/sqrt(n)`.  At the support endpoint `log n=2a`, the shifted
   cosine has measure-zero overlap, so including or excluding equality does
   not change the bound.  Prime powers are counted once via `Lambda(n)`.

5. **Projection and derivative signs.**  Suzuki uses `D=i d/dx`; hence
   `Ds_j=i(pi j/a^(3/2))c_j`.  The two factors `i` and `conj(i)` contribute
   `+1`.  Since `integral c_j=0`, `P_a Ds_j=Ds_j`.  The left projection in
   `G_a=P_aGP_a` contributes a constant function, which is orthogonal to
   `Ds_j`.  Thus projections introduce no hidden row or rank-one term.  A
   direct polarized derivation with `g=-Psi` gives the displayed global
   minus sign in (4).  The sign is therefore reconciled even though the
   absolute tail inequalities do not depend on it.

6. **Matrix orientation.**  If low columns are indexed by `k<=N`, high
   coefficients by `l>N`, and `Y` maps low vectors into high coordinates,
   then row `l` of `Y` is a vector `Y_l` and
   `R_j=sum_l H_jl Y_l-H_{j,low}`.  The derivation of (3) uses row Euclidean
   norms and then the Frobenius majorant.  If a codebase stores `Y` transposed,
   (3) must be transposed too; the scalar bound (1) is orientation-free.

7. **Uniformity.**  The proof gives a fixed-`a` theorem and a compact
   `[a_minus,a_plus]` theorem.  It does not give a uniform estimate down to
   `a=0`, and it does not address `a` tending to infinity.  Either cofinal
   passage is a separate theorem.

Accordingly, the safe current label is **human theorem, independently
normalization-audited; not Lean-formalized**.  Items 1, 2, and 5 have been
reconstructed above.  The remaining limitations are downstream: no effective
cofinal weighted decay, no completed Schur certificate, and no RH conclusion.
