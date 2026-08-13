# Navier–Stokes — sharp dissipation cost of a Barker–Popkin Orlicz spike

Date: 2026-08-13 UTC  
Primary literature interface: Tobias Barker and Henry Popkin, *Quantitative estimates for the forced Navier–Stokes equations and applications*, arXiv:2602.09951v1 (2026), Theorem 4.2.2.

**Status:** PROVED reusable functional inequality; PROVED Leray–Hopf time-integrated corollary; PROVED matching one-scale sharpness model; NOT a global-regularity theorem; FIVE-ALARM OFF.

## 1. Setup

Let

\[
\Phi(s)=\frac{s^3}{L(s)^\theta},\qquad 0<\theta<1,
\]

where `L` is the positive increasing triple-logarithmic factor in Barker–Popkin's local Orlicz criterion. Choose `S_*` so large that `L(s) >= 1` and `L` is increasing for `s >= S_*`.

For a measurable region `B` and a vector field `u in H^1(R^3)`, define the continuous truncated local charge

\[
M_B(u)=\int_B[\Phi(|u|)-\Phi(S_*)]_+\,dx.
\tag{1.1}
\]

This is the convenient record variable: for smooth `u` on a bounded cylinder it is continuous in time, and Barker–Popkin divergence of `int_B Phi(|u|)` is equivalent to divergence of `M_B(u)` up to the fixed finite contribution `Phi(S_*)|B|`.

Write

\[
E=\|u\|_2^2,\qquad D=\|\nabla u\|_2^2.
\]

No Navier–Stokes equation is used until Section 3.

## 2. Sharp spike-cost inequality

### Theorem NS-BP-SC1

There is a constant `c>0`, depending only on the Sobolev constant and the fixed source weight, such that whenever

\[
M:=M_B(u)\ge 2ES_*,
\]

one has

\[
\boxed{
D\ge
cE^{-1}M^{4/3}
L\!\left(\frac{M}{2E}\right)^{4\theta/3}.
}
\tag{2.1}
\]

The conclusion is understood trivially when `E=0`, because then `u=0` and `M=0`.

### Proof

Set

\[
A=\frac{M}{2E}\ge S_*.
\]

On `S_* <= |u| <= A`, the bound `L>=1` gives

\[
[\Phi(|u|)-\Phi(S_*)]_+
\le\Phi(|u|)
\le |u|^3
\le A|u|^2.
\]

Therefore the contribution from `|u| <= A` is at most

\[
AE=\frac M2.
\]

At least half of the truncated charge lies above `A`:

\[
\frac M2
\le
\int_{B\cap\{|u|>A\}}[\Phi(|u|)-\Phi(S_*)]_+dx
\le
\int_{B\cap\{|u|>A\}}\Phi(|u|)dx.
\]

Because `L` is increasing,

\[
\frac M2
\le
L(A)^{-\theta}\int_{\mathbb R^3}|u|^3dx.
\]

The three-dimensional Gagliardo–Nirenberg inequality gives

\[
\|u\|_3^3
\le C\|u\|_2^{3/2}\|\nabla u\|_2^{3/2}
=CE^{3/4}D^{3/4}.
\]

Thus

\[
M\le CE^{3/4}D^{3/4}L(A)^{-\theta}.
\]

Raise to the `4/3` power and substitute `A=M/(2E)` to obtain `(2.1)`.

### Interpretation

A large local Barker–Popkin charge cannot be free on an energy slice. Its instantaneous enstrophy cost is superlinear in the charge, with the exact extra logarithmic factor

\[
M^{4/3}L(M/E)^{4\theta/3}.
\]

## 3. Leray–Hopf time-budget corollary

Let `u` be a Leray–Hopf solution with viscosity `nu>0` and initial kinetic energy

\[
E_0=\|u_0\|_2^2.
\]

For a fixed region `B`, put `M(t)=M_B(u(t))`. The energy inequality gives

\[
\|u(t)\|_2^2\le E_0,
\qquad
2\nu\int_0^T\|\nabla u(t)\|_2^2dt\le E_0.
\]

On the set `M(t) >= 2 E_0 S_*`, Theorem NS-BP-SC1 and monotonicity of `L` imply

\[
\|\nabla u(t)\|_2^2
\ge
cE_0^{-1}M(t)^{4/3}
L\!\left(\frac{M(t)}{2E_0}\right)^{4\theta/3}.
\]

Integrating yields the finite spike budget

\[
\boxed{
\int_{\{0<t<T:\,M(t)\ge2E_0S_*\}}
M(t)^{4/3}
L\!\left(\frac{M(t)}{2E_0}\right)^{4\theta/3}dt
\le
C\frac{E_0^2}{\nu}.
}
\tag{3.1}
\]

Consequently, for every `K >= 2 E_0 S_*`,

\[
\boxed{
|\{0<t<T:M(t)\ge K\}|
\le
C\frac{E_0^2}
{\nu K^{4/3}L(K/(2E_0))^{4\theta/3}}.
}
\tag{3.2}
\]

Barker–Popkin prove that at a singular point the corresponding local charge has unbounded limsup. Equations `(3.1)`–`(3.2)` force any such divergence to occur through increasingly narrow time spikes. They do not by themselves exclude those spikes.

## 4. Sharpness under energy and Sobolev information

Choose a fixed nonzero compactly supported smooth divergence-free field `psi`, and for large amplitude `A` define

\[
u_A(x)=A\psi\!\left(\frac{x-x_0}{r_A}\right),
\]

where `r_A` is chosen so that `||u_A||_2^2=E`. Then

\[
r_A\asymp E^{1/3}A^{-2/3},
\]

and direct scaling gives

\[
D_A:=\|\nabla u_A\|_2^2
\asymp E^{1/3}A^{4/3},
\tag{4.1}
\]

\[
M_B(u_A)
\asymp \frac{EA}{L(A)^\theta}.
\tag{4.2}
\]

The subtraction of `Phi(S_*)` contributes only `O(EA^{-2})` and does not affect `(4.2)`. The iterated logarithm is slowly varying, so

\[
L\!\left(\frac{M_B(u_A)}E\right)\asymp L(A).
\]

Substituting `(4.2)` into the right side of `(2.1)` gives a quantity comparable to `(4.1)`. Hence the powers `E^{-1}`, `M^{4/3}`, and `L^{4\theta/3}` cannot be improved using only one-slice energy and Sobolev information.

The parabolic diffusion time of the packet is

\[
r_A^2\asymp E^{2/3}A^{-4/3}
\asymp
E^2M_B(u_A)^{-4/3}
L\!\left(\frac{M_B(u_A)}E\right)^{-4\theta/3}.
\tag{4.3}
\]

Thus the reciprocal of the instantaneous spike cost is exactly the natural one-packet diffusion time, up to constants and slow variation.

## 5. Exact remaining dynamic gate

The functional estimate reaches its natural scaling limit. A contradiction now requires equation-specific temporal persistence or fresh-charge structure.

### `NS-DYNAMIC-DINI-NO-RETURN`

For every sufficiently large record value `K` of the local Barker–Popkin charge near a hypothetical singular point, prove one of:

1. the charge remains at a fixed fraction of `K` for a time comparable to
   \[
   E_0^2K^{-4/3}L(K/E_0)^{-4\theta/3};
   \]
2. its rapid disappearance creates a quantitatively comparable, disjoint local-energy/pressure/vorticity flux charge;
3. the charge decomposes into low-critical-mass amplitude shells, each diffusion-dominated and eliminated by localized epsilon-regularity/Carleman propagation.

The companion countermodels show that energy, weak-`L^3`, exact axisymmetry, and bounded circulation do not imply this theorem. The Navier–Stokes equation, local pressure, and quantitative propagation must perform essential work.

Barker–Popkin's forced localization estimates and Barker's quantitative physical-space propagation of vorticity concentration are the strongest current primary mechanisms aligned with this gate.

## 6. Hostile scope audit

- `(2.1)` is a functional inequality for arbitrary `H^1` fields.
- `(3.1)` uses only the Leray–Hopf energy inequality after `(2.1)`.
- Unbounded limsup plus finite weighted time integral is not a contradiction.
- The one-packet model proves sharpness only relative to energy/Sobolev information; it is not a Navier–Stokes solution.
- No persistence, pressure, or Carleman theorem is silently assumed.
- No Clay theorem is claimed.

\[
\boxed{\text{FIVE-ALARM OFF.}}
\]
