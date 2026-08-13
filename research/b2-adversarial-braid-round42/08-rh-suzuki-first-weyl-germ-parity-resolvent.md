# Riemann hypothesis — Suzuki's first normalized Weyl-germ coefficient is a parity-resolvent imbalance

Date: 2026-08-13 UTC

Branch: `automation/b2-round42-repsat-optimal-linear-sketch-20260813`

Exact parent: `stevemoraco/qs@042c322b1f21239112dc2da8775402adbc568c47`

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 📚 SOURCE-VERIFIED against Masatoshi Suzuki, arXiv:2606.09096v1, Theorem 1.5 and Section 6; 🟢 PROVED an exact derivative formula for the normalized finite Weyl function; 🟢 PROVED its gauge-invariant parity-resolvent form; 🧩 isolates the first scalar datum required by the banked Weyl-germ route; 🔴 REFUTED the idea that matching this one derivative identifies the germ; 🔵 LEAN-SOURCE staged separately; ✅ LEAN-VERIFIED pending replay. **NOT RH. FIVE-ALARM OFF.**

---

## 0. Inherited normalized Weyl family

Write Suzuki's characteristic function as

\[
W(a,\theta;z)=A_a(z)+e^{i\theta}B_a(z),
\]

where

\[
A_a(z)
=(z-i)P_a(z),
\qquad
P_a(z)=\int_{-a}^a v_+(a,x)e^{izx}\,dx,
\]

and

\[
B_a(z)
=(z+i)Q_a(z),
\qquad
Q_a(z)=\int_{-a}^a v_-(a,x)e^{izx}\,dx.
\]

The round-42 banked RH note proves from Suzuki's all-boundary-phase real-zero theorem that

\[
S_a(z)=-A_a(z)/B_a(z)
\]

is a Schur function on the upper half-plane with `S_a(i)=0`. Its Cayley transform

\[
M_a(z)
=i\frac{1+S_a(z)}{1-S_a(z)}
=-i\frac{W(a,\pi;z)}{W(a,0;z)}
\]

is a normalized Herglotz function satisfying

\[
M_a(i)=i.
\]

The value at `i` is automatic for every cutoff and contains no limiting arithmetic information. The first nontrivial datum is the derivative.

---

# CLAIMANT

## 1. Exact finite derivative formula

### Theorem RH-WEYLR42-1

For every admissible cutoff and shift,

\[
\boxed{
M_a'(i)=-\frac{P_a(i)}{Q_a(i)}.
}
\tag{1.1}
\]

### Proof

Set

\[
N=A-B,
\qquad
D=A+B.
\]

At `z=i`,

\[
A(i)=0,
\qquad
B(i)=2iQ(i)\ne0.
\]

Differentiate the quotient:

\[
\left(\frac ND\right)'(i)
=
\frac{(A'-B')B-(-B)(A'+B')}{B^2}
=
\frac{2A'(i)}{B(i)}.
\]

Since `A'(i)=P(i)` and `M=-iN/D`,

\[
M'(i)
=-i\frac{2P(i)}{2iQ(i)}
=-\frac{P(i)}{Q(i)}.
\]

∎

## 2. Gauge-invariant modulus

The deficiency vectors have independent phase choices

\[
v_+\mapsto e^{i\alpha}v_+,
\qquad
v_-\mapsto e^{i\beta}v_-.
\]

Consequently

\[
M_a'(i)
\mapsto
 e^{i(\alpha-\beta)}M_a'(i).
\]

Thus the phase can rotate the derivative but cannot change

\[
\boxed{|M_a'(i)|.}
\tag{2.1}
\]

Any source-specific germ limit must first match this modulus.

## 3. Resolvent form

Suzuki's Section 6 identifies the deficiency vectors through the positive shifted operator

\[
T_{a,\lambda}=A_a-\lambda I,
\qquad
\lambda<\lambda_a,
\]

by

\[
T_{a,\lambda}v_+=e^x,
\qquad
T_{a,\lambda}v_-=e^{-x},
\]

with the paper's sign convention.

Let

\[
R_{a,\lambda}=T_{a,\lambda}^{-1},
\qquad
f_+=e^x,
\qquad
f_-=e^{-x}.
\]

With canonical real/reflection-compatible phases,

\[
P_a(i)
=\langle R_{a,\lambda}f_+,f_-\rangle,
\]

and

\[
Q_a(i)
=\langle R_{a,\lambda}f_-,f_-\rangle.
\]

The localized Weil operator and the interval are reflection symmetric. Hence the resolvent commutes with reflection and

\[
\langle Rf_+,f_+\rangle
=
\langle Rf_-,f_-\rangle.
\]

Cauchy--Schwarz in the positive `R`-inner product gives

\[
|P_a(i)|\le Q_a(i),
\]

which is the derivative form of Schwarz--Pick:

\[
|M_a'(i)|\le1.
\]

## 4. Even/odd parity decomposition

Put

\[
c(x)=\cosh x,
\qquad
s(x)=\sinh x,
\]

so that

\[
f_+=c+s,
\qquad
f_-=c-s.
\]

Reflection symmetry makes the even and odd sectors resolvent-orthogonal. Define

\[
E_{a,\lambda}
=\langle R_{a,\lambda}c,c\rangle,
\qquad
O_{a,\lambda}
=\langle R_{a,\lambda}s,s\rangle.
\]

Both are nonnegative, and

\[
P_a(i)=E_{a,\lambda}-O_{a,\lambda},
\]

\[
Q_a(i)=E_{a,\lambda}+O_{a,\lambda}.
\]

Therefore

\[
\boxed{
|M_a'(i)|
=
\frac{|E_{a,\lambda}-O_{a,\lambda}|}
{E_{a,\lambda}+O_{a,\lambda}}.
}
\tag{4.1}
\]

This is the first gauge-free Weyl-germ invariant: the normalized imbalance between the even and odd resolvent energies of the two exponential deficiency sources.

---

## 5. Exact xi target

Set

\[
X(z)=\xi(1/2-iz),
\qquad
L(s)=\frac{\xi'(s)}{\xi(s)},
\qquad
c_\xi=L(3/2)>0.
\]

The normalized target is

\[
M_\xi(z)
=-\frac{X'(z)}{c_\xi X(z)}.
\]

Since

\[
M_\xi(z)
=
\frac{i}{c_\xi}L(1/2-iz),
\]

differentiation gives

\[
\boxed{
M_\xi'(i)
=
\frac{L'(3/2)}{L(3/2)}
=
\frac{(\log\xi)''(3/2)}{(\log\xi)'(3/2)}.
}
\tag{5.1}
\]

This formula is unconditional as a meromorphic/Taylor identity because `xi(3/2)` and `xi'(3/2)` are nonzero.

## 6. Necessary first-germ theorem

Any locally uniform convergence

\[
M_a\to M_\xi
\]

near `i` forces derivative convergence. The weaker countable-germ hypothesis from the parent note also forces it: normality plus pointwise identification on a set accumulating at `i` makes every subsequential limit equal to `M_xi`, hence the whole family converges locally uniformly.

Therefore the banked `RH-SUZUKI-WEYL-GERM` theorem requires

\[
\boxed{
\frac{|E_{a,\lambda(a)}-O_{a,\lambda(a)}|}
{E_{a,\lambda(a)}+O_{a,\lambda(a)}}
\longrightarrow
\left|
\frac{(\log\xi)''(3/2)}{(\log\xi)'(3/2)}
\right|.
}
\tag{6.1}
\]

A relative phase must additionally align the complex sign of `M_a'(i)` with the target.

This is now the cheapest scalar falsifier for any proposed choice of shifts and phases.

---

# CRITIC

## 7. One derivative does not identify the germ

Let `0<=kappa<1` and choose `epsilon>0` with

\[
\kappa+\epsilon\le1.
\]

On the unit disk define

\[
f_0(w)=\kappa w,
\qquad
f_1(w)=\kappa w+\epsilon w^2.
\]

Both are Schur functions because for `|w|<1`,

\[
|f_1(w)|\le\kappa|w|+\epsilon|w|^2<\kappa+\epsilon\le1.
\]

They satisfy

\[
f_0(0)=f_1(0)=0,
\qquad
f_0'(0)=f_1'(0)=\kappa,
\]

but they are different functions. Their Cayley transforms are distinct normalized Herglotz functions with the same first derivative at the normalization point.

### Critic verdict

🔴 **REFUTED:** matching `M_a(i)` and `M_a'(i)` is enough to identify the xi Weyl germ.

The first derivative is a necessary scalar gate, not a sufficient RH theorem. Higher Taylor coefficients or values on an accumulating set remain load-bearing.

## 8. Shift dependence remains real

The resolvent

\[
R_{a,\lambda}=(A_a-\lambda I)^{-1}
\]

depends on the admissible shift. Equation `(6.1)` is therefore not a property of the cutoff `a` alone. Any proof must specify `lambda(a)<lambda_a` and control the even and odd resolvent energies uniformly as both the interval and shift vary.

Normal-family compactness does not select this ratio.

---

# REBUILDER

## 9. Exact next calculation

The first-order Weyl-germ route is reduced to a parity-resolvent theorem:

> Choose admissible shifts `lambda(a)<lambda_a` so that the even/odd resolvent imbalance `(6.1)` converges to the xi logarithmic-derivative ratio, then compute and match the second and higher normalized parity-resolvent moments.

The parity decomposition suggests two possible interfaces:

1. spectral measures of `A_a` in the even and odd sectors tested against `cosh` and `sinh`;
2. exact Fredholm/resolvent equations for the two scalar energies `E_{a,lambda}` and `O_{a,lambda}`.

A failure of `(6.1)` for every admissible shift family kills the current Weyl-germ route before any global meromorphic analysis.

### 🚧 Exact remaining gap

- a source-specific asymptotic for `E_{a,lambda}` and `O_{a,lambda}`;
- a canonical shift and relative phase;
- all higher germ coefficients or an accumulating-set limit;
- the Herglotz property of `M_xi`;
- RH.

---

## 10. Lean status

A companion Lean file formalizes only finite algebraic cores:

- quotient differentiation at a point with `A=0`;
- the parity ratio `(E-O)/(E+O)` and its absolute bound;
- the exact target logarithmic-derivative quotient as an abstract scalar;
- two distinct disk polynomials with equal value and derivative at zero.

It does not formalize complex holomorphy, Suzuki's operators, resolvents, xi, Schwarz--Pick, or RH.

## 11. Provenance

- Primary source: Masatoshi Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v1, Theorem 1.5 and Sections 6.2--6.4.
- Parent normalized Herglotz note: `stevemoraco/RH@9dd3c2f7ddffdd74ccb7e1f252626836902e4830`.
- Exact round-42 branch ancestor: `stevemoraco/qs@e345ef906a7b809e3c47e949e556b6417247ed06`.

**FIVE-ALARM OFF.**
