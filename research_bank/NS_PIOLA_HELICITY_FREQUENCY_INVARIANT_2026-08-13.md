# Exact Piola helicity–frequency invariant and packet-energy debt

**Date:** 2026-08-13  
**Status:** GREEN finite-dimensional transport identity; architecture-level Navier–Stokes obstruction only.  
**Scope:** contravariant Piola/Cauchy transport by volume-preserving linear maps. It is not the full nonlinear Navier–Stokes evolution and not the Kelvin law for a linearized velocity perturbation. No Lean verification is claimed.

## 1. Setup

Let \(\xi\in\mathbb R^3\setminus\{0\}\), \(s\in\{\pm1\}\), and let
\(b\in\mathbb C^3\) be a unit \(s\)-helical transverse polarization:
\[
\xi\cdot b=0,\qquad
i\xi\times b=s|\xi|b,\qquad
|b|=1.
\]
Let \(F\in SL(3,\mathbb R)\), and define the Piola-transported covector and carrier
\[
k=F^{-T}\xi,\qquad B=Fb.
\]
Put
\[
G=|B|,\qquad \widehat k=\frac{k}{|k|},\qquad
H_kB=i\widehat k\times B.
\]
Define the opposite-helicity defect
\[
\varepsilon=\frac{|H_kB-sB|}{|B|}.
\]

Because
\[
k\cdot B=(F^{-T}\xi)\cdot(Fb)=\xi\cdot b=0,
\]
the transported carrier remains transverse.

## 2. Exact vector invariant

For every real \(F\in SL(3,\mathbb R)\),
\[
(Fx)\times(Fy)=F^{-T}(x\times y).
\]
The initial helical normalization implies
\[
ib\times\overline b=s\frac{\xi}{|\xi|}.
\]
Therefore
\[
\boxed{
iB\times\overline B
 =F^{-T}(ib\times\overline b)
 =s\frac{k}{|\xi|}.
}
\]
Taking the inner product with \(\widehat k\) gives
\[
\boxed{
\langle B,H_kB\rangle
 =s\frac{|k|}{|\xi|}.
}
\]

## 3. Exact helicity decomposition

On the transverse plane define
\[
P_{\pm}=\frac{I\pm H_k}{2}.
\]
Write
\[
r=\frac{|k|}{|\xi|}.
\]
Since \(H_k\) is a self-adjoint involution on \(k^\perp\),
\[
|P_sB|^2+|P_{-s}B|^2=G^2,
\]
while the invariant gives
\[
|P_sB|^2-|P_{-s}B|^2=r.
\]
Hence
\[
\boxed{
|P_sB|^2=\frac{G^2+r}{2},\qquad
|P_{-s}B|^2=\frac{G^2-r}{2}.
}
\]

Moreover,
\[
H_kB-sB=-2sP_{-s}B,
\]
so
\[
\varepsilon^2
 =\frac{4|P_{-s}B|^2}{G^2}.
\]
Eliminating \(P_{-s}B\) yields the sharp identity
\[
\boxed{
\frac{|k|}{|\xi|}
 =G^2\left(1-\frac{\varepsilon^2}{2}\right).
}
\]

There is no inequality loss: all transported carrier gain not paid as covector-frequency growth is exactly opposite-helicity energy.

## 4. Consequences

### Corollary 4.1 — bounded-frequency, small-helicity-mixing obstruction

If
\[
\frac{|k|}{|\xi|}=1+o(1),
\qquad
\varepsilon=o(1),
\]
then
\[
G=1+o(1).
\]
Thus a Piola carrier cannot acquire large amplitude while simultaneously retaining its frequency scale and helicity sign.

More quantitatively, if \(G\ge M\) and \(\varepsilon\le e<\sqrt2\), then
\[
\frac{|k|}{|\xi|}
 \ge M^2\left(1-\frac{e^2}{2}\right).
\]

### Corollary 4.2 — finite orthogonal ensemble

Let carriers \(b_j\) have initial squared norms \(a_j^2\), signs \(s_j\), transported carriers \(B_j\), and ratios
\[
r_j=\frac{|k_j|}{|\xi_j|}.
\]
Summing the exact component identity gives
\[
E:=\sum_j|B_j|^2
 =\sum_j r_ja_j^2+2E_{\mathrm{opp}},
\]
where
\[
E_{\mathrm{opp}}=\sum_j|P_{-s_j}B_j|^2.
\]
If
\[
r_j\le R\quad\text{for all }j,
\qquad
E_{\mathrm{opp}}\le\eta E,\quad \eta<\frac12,
\]
then, with \(E_0=\sum_ja_j^2\),
\[
\boxed{
\frac{E}{E_0}\le\frac{R}{1-2\eta}.
}
\]
This applies directly to an orthogonal or microlocally orthogonal carrier decomposition. Cross-carrier interference and nonorthogonality are outside the statement.

## 5. Claim / counterpressure / salvage

**Claimant.** A volume-preserving deformation might amplify a helical high-frequency packet while leaving its shell and helicity almost unchanged.

**Critic.** The exact identity forces the gain to appear either as quadratic covector-frequency growth or as opposite-helicity energy. No affine volume-preserving shear evades this accounting.

**Rebuilder.** A viable Navier–Stokes packet mechanism must pay through at least one load-bearing channel:

1. frequency migration;
2. helicity mixing;
3. cross-carrier nonorthogonality/interference;
4. curvature or nonaffine commutator error;
5. a transport law different from contravariant Piola/Cauchy transport;
6. a genuinely nonlinear residual/cancellation.

This is an exact architecture obstruction, not a regularity proof.

## 6. Scope firewall

- The theorem is pointwise finite-dimensional linear algebra.
- It applies to \(B=Fb\), \(k=F^{-T}\xi\) with \(\det F=1\).
- It does not identify an actual Navier–Stokes solution with such a carrier.
- It does not control viscosity, pressure, nonlinear packet interactions, or WKB curvature errors.
- It does not prove regularity or blow-up.

No Millennium claim is made.
