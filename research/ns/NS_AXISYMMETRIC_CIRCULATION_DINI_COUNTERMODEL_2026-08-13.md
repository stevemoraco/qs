# Navier–Stokes — axisymmetry and bounded circulation do not control Barker–Popkin Dini charge

Date: 2026-08-13 UTC  
Primary interfaces: Barker–Popkin arXiv:2602.09951v1, Theorem 4.2.2; the axisymmetric circulation variable `Gamma = r u^theta` used in Shahmurov arXiv:2606.07869v1.

**Status:** PROVED smooth finite-block axisymmetric divergence-free countermodel; PROVED smooth-on-`t<0` Leray-energy-class countermodel with uniformly bounded circulation; NOT a Navier–Stokes solution; FIVE-ALARM OFF.

## 1. Target

Let

\[
\Phi(s)=\frac{s^3}{L(s)^\theta},
\qquad 0<\theta<1,
\]

with `L` the Barker–Popkin triple-logarithmic weight. The question is whether axisymmetry, finite energy, and

\[
\|\Gamma\|_\infty,
\qquad
\Gamma=ru^\theta,
\]

can force a uniform bound on `int Phi(|u|)`. The answer is no at the level of function-space information.

## 2. Toroidal building blocks

Choose nonzero cutoffs `psi,chi in C_c^infinity((-1,1))`, bounded below on `(-1/2,1/2)`. For `n>=2`, set

\[
A_n=2^n,
\qquad
\varepsilon_n=n^{-1/2},
\qquad
r_n=c_rA_n^{-1},
\qquad
\rho_n=c_\rho A_n^{-1},
\qquad
\ell_n=c_z\varepsilon_nA_n^{-1},
\]

with `0<c_rho<c_r/4`. Choose disjoint axial intervals centered at `z_n`, and define the pure-swirl field

\[
b_n(r,z)=
A_n
\psi\!\left(\frac{r-r_n}{\rho_n}\right)
\chi\!\left(\frac{z-z_n}{\ell_n}\right)e_\theta.
\tag{2.1}
\]

Each `b_n` is smooth on `R^3`, because it vanishes in a neighborhood of the axis. It is axisymmetric and divergence-free. The supports are disjoint and

\[
|\operatorname{supp}b_n|
\asymp r_n\rho_n\ell_n
\asymp\varepsilon_nA_n^{-3}.
\tag{2.2}
\]

On a fixed-fraction core, `|b_n| >= c A_n`.

## 3. Uniform circulation bound

On the support of `b_n`, `r asymp A_n^{-1}`. Hence

\[
\boxed{
\|r(b_n)^\theta\|_\infty\le C
}
\tag{3.1}
\]

uniformly in `n`. Every finite disjoint sum

\[
g_{N,M}=\sum_{n=N}^M b_n
\]

therefore satisfies

\[
\boxed{
\|r g_{N,M}^\theta\|_\infty\le C.
}
\tag{3.2}
\]

## 4. Energy and weak-`L^3` smallness

From `(2.2)`,

\[
\|b_n\|_2^2\asymp\varepsilon_nA_n^{-1}.
\]

Thus

\[
\|g_{N,M}\|_2^2
\lesssim\sum_{n=N}^M\varepsilon_n2^{-n}
\to0
\quad(N\to\infty)
\]

uniformly in `M>=N`.

For a threshold comparable to `A_j`,

\[
A_j^3|\{|g_{N,M}|>cA_j\}|
\lesssim
\sum_{n=j}^M\varepsilon_n2^{-3(n-j)}
\lesssim\varepsilon_j.
\]

Hence

\[
\boxed{
\|g_{N,M}\|_{L^{3,\infty}}^3\lesssim\varepsilon_N,
\qquad
\|g_{N,M}\|_{L^{3,\infty}}\lesssim N^{-1/6}.
}
\tag{4.1}
\]

## 5. Divergent Barker–Popkin charge

The core lower bound gives

\[
\int\Phi(|g_{N,M}|)dx
\gtrsim
\sum_{n=N}^M
\frac{\varepsilon_n}{L(c2^n)^\theta}.
\tag{5.1}
\]

The triple logarithm grows more slowly than every positive power of `n`, so the infinite series diverges. Therefore for every `N` and target `K`, one can choose finite `M=M(N,K)` such that

\[
\int\Phi(|g_{N,M}|)dx\ge K,
\]

while `(3.2)` and `(4.1)` hold.

### Theorem NS-ACD1

There is a sequence of smooth compactly supported axisymmetric divergence-free pure-swirl fields `g_k` such that

\[
\|r g_k^\theta\|_\infty\le C,
\qquad
\|g_k\|_2\to0,
\qquad
\|g_k\|_{L^{3,\infty}}\to0,
\]

but

\[
\boxed{
\int\Phi(|g_k|)dx\to\infty.
}
\tag{5.2}
\]

## 6. Finite total Dirichlet action in spacetime

For the toroidal blocks,

\[
\|\nabla g_{N,M}\|_2^2
\lesssim
\sum_{n=N}^M\frac{A_n}{\varepsilon_n}<\infty.
\]

Choose blocks `g_k` from Theorem NS-ACD1 and pairwise disjoint time intervals `I_k` accumulating only at `0`. Let `eta_k in C_c^infinity(I_k)` attain one, and choose

\[
|I_k|\|\nabla g_k\|_2^2\le2^{-k}.
\]

Then

\[
v(x,t)=\sum_k\eta_k(t)g_k(x)
\]

is smooth for `t<0`, axisymmetric, divergence-free, pure swirl, and satisfies

\[
\sup_{t<0}\|r v^\theta(t)\|_\infty\le C,
\]

\[
v\in L_t^\infty L_x^2\cap L_t^2\dot H_x^1.
\]

At selected times `t_k -> 0`, the weak-`L^3` and `L^2` norms vanish while the local Barker–Popkin charge diverges.

## 7. Consequence

Exact axisymmetry, the circulation maximum-principle quantity, finite kinetic energy, finite total Dirichlet action, and even vanishing weak-`L^3` slices do not provide the missing Dini payment law. Any successful proof must use the Navier–Stokes equation, local energy inequality, pressure coupling, or quantitative temporal propagation.

\[
\boxed{\text{FIVE-ALARM OFF.}}
\]
