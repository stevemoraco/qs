# LCI and isolated-singularity no-gos for the theta-secant surface target

**Date:** 2026-08-13  
**Status:** GREEN exact no-go theorems over \(\mathbf C\). Not a Hodge-conjecture result.  
**Scope:** reduced pure codimension-two lci subvarieties of abelian fourfolds. Arbitrary non-lci CM surfaces and lci surfaces with positive-dimensional singular locus remain open, except for the global-complete-intersection case below.

## 1. Forced invariants

Let \(X\) be a principally polarized abelian fourfold, \(x=c_1(\Theta)\), and \(d=24k-1\), \(k\ge1\). A rank-one target
\[
I_Z(\Theta)
\]
with Chern character
\[
v_d
 =1+x-\frac d2x^2-\frac d6x^3+\frac{d^2}{24}x^4
\]
forces
\[
\operatorname{ch}(\mathcal O_Z)
 =12kx^2-8kx^3+(-24k^2+4k)x^4.
\]
Since \(\operatorname{td}(X)=1\),
\[
\boxed{
\chi(\mathcal O_Z)
 =\int_X\operatorname{ch}_4(\mathcal O_Z)
 =96k(1-6k)<0.
}
\]

Assume now that \(Z\hookrightarrow X\) is a regular embedding of codimension two, with normal bundle
\[
N=(I_Z/I_Z^2)^\vee.
\]
Because \(\omega_X\simeq\mathcal O_X\),
\[
\omega_Z\simeq\det N.
\]
Put
\[
K=c_1(\omega_Z).
\]
The virtual tangent class is
\[
T_Z^{\mathrm{vir}}=T_X|_Z-N,
\]
and virtual Noether/RR gives
\[
\boxed{
12\chi(\mathcal O_Z)
 =K^2+\deg c_2(T_Z^{\mathrm{vir}}).
}
\]

For reference, GRR and self-intersection determine the numerical virtual Chern data:
\[
\int_Zc_2(N)
 =\int_X[Z]^2
 =(12kx^2)^2
 =3456k^2,
\]
\[
\int_ZK^2=576k(1-3k),
\]
and
\[
\boxed{
\deg c_2(T_Z^{\mathrm{vir}})
 =576k(1-9k)<0.
}
\]
These identities are consistent with virtual Noether.

## 2. The canonical line bundle is nef when singularities are isolated

Assume that \(Z\) is reduced and has only isolated singularities. Translation-invariant vector fields give
\[
\mathcal O_Z^{\oplus4}=T_X|_Z\longrightarrow N.
\]
This is surjective on \(Z_{\mathrm{reg}}\). Taking the second exterior power gives global sections of
\[
\det N=\omega_Z
\]
whose common base locus is contained in the finite singular set.

Every integral curve in \(Z\) has generic point outside this finite base locus. Some global section of \(\omega_Z\) is nonzero at that generic point, and its restriction gives an effective divisor on the curve. Hence
\[
\deg(\omega_Z|_C)\ge0
\]
for every integral curve \(C\). Thus \(\omega_Z\) is nef, and
\[
K^2\ge0.
\]
Already the virtual Noether formula and \(\chi(\mathcal O_Z)<0\) imply
\[
\deg c_2(T_Z^{\mathrm{vir}})<0.
\]

## 3. Topology forces the opposite sign

Elduque–Geske–Maxim prove that every pure \(n\)-dimensional lci closed subvariety of a complex abelian variety has signed topological Euler characteristic
\[
(-1)^n\chi_{\mathrm{top}}(Z)\ge0.
\]
For a surface,
\[
\chi_{\mathrm{top}}(Z)\ge0.
\]

At an isolated complete-intersection surface singularity, the Milnor fibre is a bouquet of \(\mu_p\) two-spheres. The local smoothing/Milnor-class formula therefore has the plus sign
\[
\boxed{
\deg c_2(T_Z^{\mathrm{vir}})
 =\chi_{\mathrm{top}}(Z)+\sum_{p\in\operatorname{Sing}Z}\mu_p.
}
\]
Both terms on the right are nonnegative, contradicting the negative virtual Chern number forced above.

### Theorem 3.1

There is no reduced pure codimension-two lci subvariety of a complex abelian fourfold, with only isolated singularities, whose ideal twisted by \(\Theta\) has Chern character \(v_{24k-1}\).

In particular, no smooth target exists.

## 4. Global complete intersections are impossible even with larger singular locus

Aluffi–Mihalcea–Schürmann–Su, Corollary 8.3, prove signed Segre–Milnor effectivity for a global complete intersection
\[
Z=\{s_1=\cdots=s_r=0\}
\]
in a smooth projective variety with globally generated tangent bundle, when the equations are sections of positive powers of a very ample line bundle. On an abelian variety and in complex dimension two, this says that
\[
\operatorname{Mi}(Z)
 =c_F(Z)-c_{\mathrm{SM}}(Z)
\]
has nonnegative degree.

For the target, the global-complete-intersection canonical bundle is nef (indeed positive in the equation directions), so virtual Noether and \(\chi(\mathcal O_Z)<0\) give
\[
\deg c_F(Z)=\deg c_2(T_Z^{\mathrm{vir}})<0.
\]
But
\[
\deg c_{\mathrm{SM}}(Z)=\chi_{\mathrm{top}}(Z)\ge0.
\]
Therefore
\[
\deg\operatorname{Mi}(Z)<0,
\]
contradicting Segre–Milnor effectivity.

### Theorem 4.1

No global complete intersection of the type covered by AMSS Corollary 8.3 realizes the theta-secant surface target, regardless of the dimension of its singular locus.

## 5. Claim / critic / rebuild

**Claim.** The pure-CM escape might be realized by a regular embedding with only finitely many singular points.

**Critic.** Its virtual Euler number is forced negative. Signed topological Euler and positive Milnor numbers force it nonnegative.

**Rebuilder.** Every surviving target must satisfy at least one of:

1. it is not lci;
2. its singular locus has positive dimension and it is not a global complete intersection covered by Segre–Milnor effectivity;
3. it is genuinely nonreduced, hence singular at its generic support points.

For a Hilbert–Burch morphism, a smooth or isolated-singular degeneracy surface is excluded. Any lci escape must carry a curve of nontransversality; any cleaner route must use a non-lci pure CM surface.

## 6. Sources and scope

- Eva Elduque, Christian Geske, Laurentiu Maxim, *On the signed Euler characteristic property for subvarieties of abelian varieties*, Journal of Singularities 17 (2018), arXiv:1801.03599.
- Paolo Aluffi, Leonardo Mihalcea, Jörg Schürmann, Changjian Su, *Positivity of Segre-MacPherson classes*, arXiv:1902.00762v2, §8.2, especially Proposition 8.2 and Corollary 8.3.
- Standard ICIS Milnor-fibre and Milnor-class formulae.

The isolated-singularity theorem is for reduced lci subvarieties. No conclusion is asserted for arbitrary nonreduced schemes or for arbitrary lci surfaces with one-dimensional singular locus. No Lean verification or Millennium claim is made.
