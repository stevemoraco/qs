# Navier–Stokes — the Part I lifted De Giorgi identity drops a nonzero bulk transport term

Date: 2026-08-13 UTC

Branch: `automation/b2-round42-repsat-optimal-linear-sketch-20260813`

Exact parent: `stevemoraco/qs@040e302751d65aff5ced29588d7a6d52e324c3e1`

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 📚 SOURCE-VERIFIED against arXiv:2605.01875v2; 🟢 PROVED exact cylindrical-divergence and weighted integration-by-parts identities; 🔴 REFUTED the use of the physical meridional velocity as divergence-free in the five-dimensional lifted measure; 🧱 the local De Giorgi estimate omits a bulk term and therefore does not follow as written. The scalar divergence core was already ✅ LEAN-VERIFIED in round 41. **NOT A NAVIER--STOKES SOLUTION OR DISPROOF. FIVE-ALARM OFF.**

## 0. Source step

The companion Part I manuscript uses

\[
G=\omega_\theta/r,
\qquad
d\mu_5=r^3drdz,
\]

and the lifted equation

\[
\partial_tG+u^r\partial_rG+u^z\partial_zG
=
\Delta_5G-\partial_z(\Gamma_e^2).
\tag{0.1}
\]

In the proof of Theorem 3.1, it tests `(0.1)` against a cutoff level truncation and says that the meridional transport is put in lifted divergence form. The displayed energy inequality retains a cutoff flux term proportional to

\[
|u|\,|\nabla_5\zeta|G_k^2,
\]

but contains no bulk divergence contribution.

## 1. Exact divergence mismatch

For a physical axisymmetric three-dimensional velocity, incompressibility is

\[
\partial_ru^r+\frac{u^r}{r}+\partial_zu^z=0.
\tag{1.1}
\]

The divergence of the same meridional components with respect to the lifted measure `r^3drdz` is

\[
\operatorname{div}_5u
=
\partial_ru^r+\frac{3u^r}{r}+\partial_zu^z.
\tag{1.2}
\]

Subtracting `(1.1)` from `(1.2)` gives

\[
\boxed{
\operatorname{div}_5u=\frac{2u^r}{r}.
}
\tag{1.3}
\]

Thus the physical meridional velocity is not divergence-free in the lifted five-dimensional measure unless `u^r=0`.

## 2. Exact missing energy term

For a smooth compactly supported scalar `H`, weighted integration by parts gives

\[
\begin{aligned}
\int
(u^r\partial_rH+u^z\partial_zH)
H\,d\mu_5
&=
\frac12\int u\cdot\nabla_5(H^2)\,d\mu_5\\
&=
-\frac12\int(\operatorname{div}_5u)H^2\,d\mu_5\\
&=
\boxed{
-\int\frac{u^r}{r}H^2\,d\mu_5.
}
\end{aligned}
\tag{2.1}
\]

With a cutoff `zeta`, the transport contribution is

\[
-\int\frac{u^r}{r}\zeta^2H^2d\mu_5
-
\int\zeta(u\cdot\nabla\zeta)H^2d\mu_5.
\tag{2.2}
\]

The second term is the displayed cutoff flux. The first is a bulk core term and survives where `zeta=1`.

For level truncations, the exact primitive differs from `H^2/2` but the same nonzero weighted divergence multiplies that primitive. It does not disappear.

## 3. Smallest explicit witness

At any point/region with `r>0` and `u^r/r` nonzero, choose a nonzero smooth `H` supported where `u^r/r` has one sign and where the cutoff equals one. Then the bulk integral in `(2.1)` is nonzero. Therefore no boundary or cutoff convention can turn the physical transport into a divergence-free lifted transport.

# CRITIC

## 4. Could the term be estimated rather than canceled?

Possibly, but that is a new theorem. The singular coefficient `u^r/r` is not the displayed cutoff-gradient term, and it is supported in the packet core. A valid estimate would need a scale-correct norm for `u^r/r`, compatibility with the five-dimensional De Giorgi iteration, and an absorption constant uniform at the first threshold.

The current text later says the drift term is absorbed using local energy and Morrey control, but the displayed right-hand side contains only `|u||grad zeta|G_k^2`; it does not state or prove a bound for the bulk term `(2.2)`.

### Critic verdict

🔴 **REFUTED:** physical 3D incompressibility makes the meridional transport divergence-free in `dmu_5`.

🧱 **THEOREM 3.1 BLOCKED AS WRITTEN:** its foundational level-set energy inequality omits the bulk transport contribution. This obstruction is independent of the source-scaling mismatch.

## 5. Relation to the earlier blow-up-paper audit

Round 41 found the complementary type error in arXiv:2604.09949v1: that paper imposed zero five-dimensional divergence on a field advertised as the physical 3D velocity. Here Part I begins with the physical 3D velocity but then uses it as though its five-dimensional weighted divergence vanished inside the energy estimate.

The same identity `(1.3)` diagnoses both failures.

# REBUILDER

## 6. Possible repairs

A corrected proof must do one of the following.

1. Retain the true physical transport and estimate
   \[
   \int(u^r/r)\Phi(G_k)d\mu_5
   \]
   in every level-set inequality with a uniform absorbable constant.
2. Transform the unknown so that the transport becomes divergence-free in the chosen weighted measure, then rederive diffusion and source terms exactly.
3. Work in the physical cylindrical measure `r dr dz`, where the meridional velocity is divergence-free, accepting the corresponding non-Euclidean form of the lifted diffusion operator.

Each repair changes the local energy and full-Dirichlet ledger and must be propagated through source selection, descendant extraction, and packet contraction.

### 🚧 Exact remaining gap

- a correct local De Giorgi energy inequality;
- a scale-uniform bound for the bulk weighted-divergence term or a new unknown/measure;
- the source-homogeneity repair from the preceding note;
- the strict bridge and global axisymmetric theorem;
- Part II's full-dimensional front end;
- the official Navier--Stokes theorem.

## 7. Lean status

The finite identity

\[
D_3=0,\quad D_5=0\Longrightarrow u^r=0
\]

and the residual relation between the two divergence laws were compiled in

`verification/b2-round41/NSClaimTypeFirewall.lean`

on exact parent head `e345ef906a7b809e3c47e949e556b6417247ed06`, with successful clean replay runs `31670525662` and `31670737919`. The weighted integration-by-parts layer is not formalized.

## 8. Provenance

Primary source checked directly:

- arXiv:2605.01875v2, equations (1)--(5) and Theorem 3.1;
- current source date: 5 May 2026.

Exact repository parent: `stevemoraco/qs@040e302751d65aff5ced29588d7a6d52e324c3e1`.

**FIVE-ALARM OFF.**
