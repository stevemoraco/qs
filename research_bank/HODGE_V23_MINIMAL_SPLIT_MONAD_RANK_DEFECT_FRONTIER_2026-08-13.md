# Minimal split monads for the v23 rank-two and rank-three bundles

**Date:** 2026-08-13  
**Status:** exact strict-monad no-go; derived rank-defect candidates survive  
**Scope:** theta-line split presentations of the two audited K-classes. A
strict monad means that the left map is a subbundle and the right map is a
bundle quotient. Mere sheaf injectivity and higher-codimension rank defects
are not excluded.

## 1. Rank-two class

The rank-two target \(E=Q^\vee\otimes L\) has the exact split identity
\[
 [E]=e^{-5x}-2e^{-4x}+e^{-2x}+3e^{2x}-e^{4x}. \tag{1}
\]
The unique degree-compatible minimal three-term placement is
\[
 2L^{-4}\xrightarrow{\alpha}
 L^{-5}\oplus L^{-2}\oplus3L^2
 \xrightarrow{\beta}L^4. \tag{2}
\]
Indeed, the \(L^{-5}\) summand cannot receive a nonzero map from
\(L^{-4}\). Consequently \(\alpha\) lands in the accessible part
\[
 L^{-2}\oplus3L^2.
\]
After tensoring by \(L^4\), a strict left map would be a constant-rank-two
subbundle
\[
 \mathcal O_X^2\hookrightarrow
 E_{\mathrm{acc}}:=L^2\oplus3L^6. \tag{3}
\]
Its quotient would have rank two. Hence the Chern classes
\(c_3(E_{\mathrm{acc}})\) and \(c_4(E_{\mathrm{acc}})\) would vanish.
Direct multiplication gives instead
\[
 c_3(E_{\mathrm{acc}})=432x^3,\qquad
 c_4(E_{\mathrm{acc}})=432x^4. \tag{4}
\]
Thus (2) cannot be a strict monad.

This does not kill (2) as a derived architecture, but the monad
incidence changes the expected defect. Write
\[
 \beta' : L^{-2}\oplus3L^2\longrightarrow L^4
\]
for the restriction of \(\beta\). Since \(\alpha\) has zero
\(L^{-5}\)-component, the equation
\[
 \beta\alpha=0 \tag{5}
\]
is exactly \(\beta'\alpha=0\). On the open locus where \(\beta'\) is
surjective, \(\alpha\) therefore factors through the rank-three bundle
\[
 K'=\ker\beta'.
\]
After tensoring by \(L^4\),
\[
 c(K'\otimes L^4)
 =\frac{(1+2x)(1+6x)^3}{1+8x}
 =1+12x+48x^2+48x^3+48x^4. \tag{6}
\]
Thus a generic map
\[
 \mathcal O_X^2\longrightarrow K'\otimes L^4
\]
has expected rank-one degeneracy in codimension two, with
Thom--Porteous class
\[
 \boxed{48x^2}. \tag{7}
\]
The expected defect is a surface, not a curve.

The map \(\beta'\) itself fails surjectivity where its four coefficient
sections vanish. Its expected zero-cycle class is
\[
 c_4(L^6\oplus3L^2)=48x^4, \tag{8}
\]
which has length \(48\int_Xx^4=1152\) under the principal-polarization
normalization. The additional component
\(L^{-5}\to L^4\), a section of \(L^9\), can in principle make the
full \(\beta\) surjective at those points.

None of these separate genericity statements proves the simultaneous
incidence locus is nonempty. Subject to \(\beta\alpha=0\), full
surjectivity of \(\beta\), and the required grade and saturation
conditions, the surviving object is expected to be a rank-two
torsion-free cohomology sheaf with a codimension-two surface defect. It is
not expected to be reflexive. Its existence, stability, simplicity, and
Hochschild evaluation remain open.

## 2. Rank-three class

Adding \(v_{23}\) gives the exact rank-three split identity
\[
 [F]=-e^{-3x}+6e^x+e^{3x}-5e^{5x}+e^{6x}+e^{7x}. \tag{6}
\]
Place \(c\) copies of \(L^5\) on the right, so the left term is
\[
 L^{-3}\oplus(5-c)L^5.
\]
Degree compatibility leaves \(0\le c\le5\).

For \(c\le2\), too many \(L^5\) source summands must inject into only
\(L^6\oplus L^7\), so constant left rank is impossible.

For \(c=3\), the relevant square block
\[
 2L^5\longrightarrow L^6\oplus L^7
\]
has determinant a section of \(L^3\). It therefore has a divisorial rank
drop.

For \(c=4\), the accessible right map is
\[
 6L\oplus L^3\longrightarrow4L^5.
\]
A bundle surjection would have rank-three kernel and therefore force the
degree-four Chern class of the virtual quotient to vanish. But
\[
 c_4\!\left(4L^5-(6L\oplus L^3)\right)=51x^4\ne0. \tag{7}
\]

For \(c=5\), a bundle surjection
\[
 6L\oplus L^3\longrightarrow5L^5
\]
would have rank-two kernel. Yet
\[
 c\!\left((6L\oplus L^3)-5L^5\right)
 =1-16x+183x^2-1760x^3+15200x^4, \tag{8}
\]
whose nonzero \(c_3\) already contradicts rank two.

Therefore no allocation in the minimal identity (6) yields a strict
vector-bundle monad for \(F\). As in the rank-two case, sheaf-injective
or sheaf-surjective maps with determinantal defects, and genuinely derived
complexes carrying extra cohomology, remain open.

## 3. Claim, critic, salvage

**Claim.** The minimal split theta-line identities (1) and (6) admit no
strict vector-bundle monad.

**Critic.** The obstruction uses constant fiber rank. It does not rule out
maps that are injective as sheaf morphisms but drop rank on a surface or a smaller locus.

**Best salvage.** The rank-two identity points to a surface-defect torsion-free candidate
with the correct K-class. Construct simultaneous maps satisfying
\(\beta\alpha=0\), prove the expected grade and saturation, and then test
simplicity and the full trace-free Hochschild action before attempting to
pair it with a rank-three candidate.

No exceptional Hodge class and no Millennium theorem is proved here.
