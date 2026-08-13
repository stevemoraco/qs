# Yang--Mills continuum reconstruction cut

Date: 2026-08-13 UTC  
Status: **exact abstract theorem and reconstruction audit; Yang--Mills remains open; no continuum Lean proof**

## Outcome

The common-exponent theorem already banked on this branch has a clean
continuum interpretation, but only after five interfaces are made explicit:

1. a continuum Euclidean theory satisfies a valid
   Osterwalder--Schrader-to-Wightman reconstruction theorem, including its
   regularity/growth hypothesis;
2. the reconstructed positive-time translations form the strongly continuous
   semigroup \(e^{-tH}\) of a nonnegative self-adjoint Hamiltonian;
3. vacuum contributions are subtracted, so the Euclidean diagonal is exactly
   a positive \(A^*\)--\(A\) spectral autocorrelation;
4. the centered observable vectors are total in the Hilbert space sector whose
   spectrum is being claimed;
5. every member has one common positive exponent, although its finite
   prefactor and onset time may depend on the member.

Under those assumptions, no uniform frame bound, summability of prefactors,
polarization identity, or common onset time is needed.  Energy exactly at the
common exponent is allowed.  The theorem excludes \([0,m)\) on the centered
sector, not \([0,m]\).

This report proves that transport theorem and identifies the smallest
continuum certificate that would make it apply.  It does **not** construct
four-dimensional quantum Yang--Mills theory and does not prove the Clay
problem.

## 1. Official target

Jaffe and Witten require, for every compact simple gauge group \(G\), a
nontrivial quantum Yang--Mills theory on \(\mathbb R^4\), with axiomatic
properties at least as strong as the cited Wightman and
Osterwalder--Schrader schemes.  In their formulation,

\[
H\Omega=0,\qquad \sigma(H)\subset[0,\infty),
\]

and a mass gap \(\Delta>0\) means

\[
\sigma(H)\cap(0,\Delta)=\varnothing.
\]

They also require local quantum fields corresponding to gauge-invariant local
polynomials in the curvature and its covariant derivatives, with the stated
short-distance asymptotic-freedom behavior.

Primary source:

- Arthur Jaffe and Edward Witten, *Quantum Yang--Mills Theory*,
  official Clay problem description, especially printed pp. 5--6:
  https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf

Thus a transfer matrix at fixed lattice spacing, a theory only on a compact
torus, or a gap in only one selected subspace is not the official theorem.

## 2. Exact vacuum-sector theorem

### Theorem 2.1 -- total centered family implies a full vacuum-sector gap

Let \(\mathcal K\) be a complex Hilbert space, let \(H\ge0\) be self-adjoint,
and let \(\Omega\in\mathcal K\) be a unit vector with \(H\Omega=0\).  Put

\[
P_\Omega=|\Omega\rangle\langle\Omega|,\qquad Q=I-P_\Omega.
\]

Let \(D\subset Q\mathcal K\) have dense linear span in \(Q\mathcal K\), and
fix a finite \(m>0\).  Suppose that for every \(v\in D\) there are finite
constants \(C_v\ge0\) and \(t_v\ge0\) such that

\[
0\le q_v(t):=\langle v,e^{-tH}v\rangle
       \le C_v e^{-mt}\qquad(t\ge t_v).
\]

Then

\[
\mathbf 1_{[0,m)}(H)Q=0,
\qquad
H\ge mQ,
\qquad
\sigma(H)\subset\{0\}\cup[m,\infty).
\]

In particular, \(\sigma(H)\cap(0,m)=\varnothing\).  Moreover
\(\ker H=\mathbb C\Omega\).

### Proof

Because \(H\Omega=0\) and \(H\) is self-adjoint, both
\(\mathbb C\Omega\) and \(Q\mathcal K\) reduce \(H\).  Fix
\(a\) with \(0\le a<m\), and set

\[
E_a=\mathbf 1_{[0,a]}(H).
\]

For \(v\in D\), the spectral theorem and positivity give

\[
q_v(t)
 =\int_{[0,\infty)} e^{-t\lambda}\,d\mu_v(\lambda)
 \ge e^{-at}\mu_v([0,a])
 =e^{-at}\|E_av\|^2 .
\]

For \(t\ge t_v\),

\[
\|E_av\|^2\le C_v e^{-(m-a)t}.
\]

The right side tends to zero, so \(E_av=0\).  The bounded projection \(E_aQ\)
therefore vanishes on a dense linear span and hence on all of
\(Q\mathcal K\).

Choose any increasing sequence \(a_n\uparrow m\).  Strong monotone
continuity of spectral projections gives

\[
\mathbf 1_{[0,m)}(H)Q
 =\operatorname*{s-lim}_{n\to\infty}E_{a_n}Q=0.
\]

The spectral measure of \(H|_{Q\mathcal K}\) is therefore supported in
\([m,\infty)\), which is exactly \(H\ge mQ\).  Since the restriction has no
zero spectral subspace and \(H\Omega=0\), the kernel is
\(\mathbb C\Omega\).  This proves all claims.  \(\square\)

### Quantifier audit

The conclusion permits spectrum at \(\lambda=m\).  An eigenvector there has
correlator \(e^{-mt}\), so no bound with exponent \(m\) could exclude it.
This is exactly compatible with the Clay interval \((0,\Delta)\).

The constants \(C_v\) and \(t_v\) may vary without any upper bound.
Diagonal correlations suffice.  The proof applies a bounded spectral
projection to each total vector separately; it never sums the constants.

## 3. Connected Euclidean \(A^*\)--\(A\) corollary

Assume the reconstructed theory supplies vectors \(A_i\Omega\) and the exact
Euclidean-time identity

\[
S_i(t)=\langle A_i\Omega,e^{-tH}A_i\Omega\rangle .
\]

This formula may be read either for bounded elements of a local observable
algebra, or for smeared fields on a common domain for which all displayed
vectors and matrix elements exist.  Put

\[
\omega(A_i)=\langle\Omega,A_i\Omega\rangle,\qquad
v_i=Q A_i\Omega.
\]

Since \(e^{-tH}\Omega=\Omega\),

\[
S_i^{\mathrm c}(t)
 :=S_i(t)-|\omega(A_i)|^2
 =\langle v_i,e^{-tH}v_i\rangle\ge0.
\]

Therefore, if

\[
\overline{\operatorname{span}}\{v_i:i\in I\}=Q\mathcal K
\]

and there is one \(m>0\) such that

\[
S_i^{\mathrm c}(t)\le C_i e^{-mt}
\quad(t\ge t_i)
\]

for finite individual \(C_i,t_i\), Theorem 2.1 proves the full gap in the
reconstructed vacuum Hilbert space.

The star on the first observable is load-bearing: it makes the diagonal a
positive spectral Laplace transform.  A general \(A\)--\(B\) connected
correlator need not be nonnegative and is not the input to the proof.

Vacuum subtraction is also load-bearing.  If \(\omega(A)\ne0\), the
unconnected autocorrelation has the constant term \(|\omega(A)|^2\) and
cannot decay to zero.  Subtracting the expectation is not a normalization
convenience; it is the exact projection from \(A\Omega\) to
\(Q\mathcal K\).

## 4. What OS reconstruction actually supplies

Osterwalder and Schrader's 1975 paper corrects the original 1973
reconstruction statement.  It explicitly notes that a technical lemma in the
first paper was wrong, so the original conditions \(E0\)--\(E4\) alone were
not then known to be sufficient.  Its corrected reconstruction uses a
strengthened distribution/linear-growth hypothesis together with Euclidean
covariance, reflection positivity, symmetry, and clustering, and obtains a
uniquely determined Wightman theory satisfying the Wightman axioms.

Primary sources:

- Konrad Osterwalder and Robert Schrader,
  *Axioms for Euclidean Green's Functions*,
  Commun. Math. Phys. 31 (1973), 83--112:
  https://doi.org/10.1007/BF01645738
- Konrad Osterwalder and Robert Schrader,
  *Axioms for Euclidean Green's Functions II*,
  Commun. Math. Phys. 42 (1975), 281--305:
  https://doi.org/10.1007/BF01608978

Consequently, the valid implication is not

\[
\text{reflection positivity alone}\Longrightarrow
\text{four-dimensional Wightman Yang--Mills}.
\]

The reconstruction interface must include the exact regularity/growth,
covariance, symmetry/locality, clustering or vacuum condition, and
nontriviality hypotheses required by the chosen rigorous reconstruction
theorem.  The Clay-specific local-field and ultraviolet requirements remain
in addition.

At the Hilbert-space stage, positive Euclidean time translations must descend
to a strongly continuous self-adjoint contraction semigroup

\[
T(t)=e^{-tH},\qquad H\ge0.
\]

A formal transfer matrix, or a semigroup before proving the reflection-null
quotient and strong continuity, does not yet provide this \(H\).

## 5. Totality: two valid routes and one invalid shortcut

### Route A -- totality by construction

In an OS construction, start with a positive-time algebra
\(\mathcal E_+\), quotient its reflection-null space, and complete.  By
definition the classes \([F]\), \(F\in\mathcal E_+\), are dense in the
reconstructed Hilbert space.  Hence the centered classes

\[
[F]^0=[F]-\langle\Omega,[F]\rangle\Omega
\]

have dense span in \(Q\mathcal K\).

This is the smallest and safest target.  Prove the common-exponent bound for
an OS-defining dense gauge-invariant family, and no separate
Reeh--Schlieder bridge is needed.

### Route B -- totality from a proved cyclicity theorem

If a reconstructed local observable algebra \(\mathcal A(\mathcal O)\) is
known to have cyclic vacuum, then

\[
\overline{\mathcal A(\mathcal O)\Omega}=\mathcal K
\]

and bounded projection by \(Q\) gives totality of the centered vectors.
The original Reeh--Schlieder theorem establishes local cyclicity in its
relativistic field-theory setting:

- Helmut Reeh and Siegfried Schlieder,
  *Bemerkungen zur Unitäräquivalenz von Lorentzinvarianten Feldern*,
  Nuovo Cimento 22 (1961), 1051--1068:
  https://doi.org/10.1007/BF02787889

Applying that name is not itself a proof that an arbitrarily selected list of
gauge-invariant polynomials is total.  One must verify the theorem's field/net,
spectrum, domain, and additivity hypotheses and show that the selected family
generates the relevant local algebra.

### Invalid shortcut -- one observable sector to every sector

Local observables in the vacuum representation do not automatically generate
vectors in other superselection representations.  The sector distinction is
structural, not a technicality:

- Sergio Doplicher, Rudolf Haag, and John E. Roberts,
  *Local Observables and Particle Statistics I*,
  Commun. Math. Phys. 23 (1971), 199--230:
  https://doi.org/10.1007/BF01877742

Thus one must make one of two honest choices:

1. state and prove the gap on the OS/Wightman vacuum Hilbert space generated
   by the Clay local gauge-invariant fields; or
2. if a larger direct sum of charged, nonlocal, or topological sectors is
   declared to be the physical Hilbert space, prove total detectors or a
   separate gap in every additional reducing sector.

Theorem 2.1 cannot see an orthogonal sector that no \(A_i\Omega\) enters.
For pure Yang--Mills the Clay statement does not separately demand a
confinement theorem, but this does not authorize silently enlarging the
Hilbert space and retaining a vacuum-sector conclusion as a full-spectrum
claim.

## 6. Claimant, critic, rebuilder

### Claimant

Construct continuum gauge-invariant Schwinger data for each compact simple
\(G\), verify a corrected OS reconstruction theorem and the Clay ultraviolet
conditions, select an OS-dense centered family, and prove one common
\(m_G>0\) in its connected diagonal Euclidean-time decay.  Theorem 2.1 then
gives

\[
\sigma(H_G)\subset\{0\}\cup[m_G,\infty),
\]

which is the official mass-gap clause.

### Critic 1 -- hidden low-energy state

Let

\[
\mathcal K=\mathbb C\Omega\oplus\mathbb Cy\oplus\mathbb Cx,\qquad
H=\operatorname{diag}(0,m,\varepsilon),
\]

where \(0<\varepsilon<m\), and test only \(D=\{y\}\).  Its exact correlator is
\(e^{-mt}\), yet \(x\) is a forbidden low-energy state.

**Killed claim.** A common exponent on an incomplete family proves the full
gap.

**Best salvage.** Prove totality in the exact Hilbert sector named in the
conclusion, or prove the omitted sector separately.

### Critic 2 -- finite time is not asymptotic time

On the one-dimensional space with \(H=\varepsilon<m\), for every finite
\(T\),

\[
e^{-\varepsilon t}
 \le e^{(m-\varepsilon)T}e^{-mt}
\qquad(0\le t\le T).
\]

**Killed claim.** An exponential fit on any finite time window excludes
lower spectrum.

**Best salvage.** Prove the bound for all \(t\ge t_v\) in the continuum
theory.  A window increasing with the regulator still requires a theorem
passing its quantifiers to the limit.

### Critic 3 -- fixed regulators do not close the continuum arrow

A positive gap at every lattice spacing or every finite volume may shrink to
zero.  A lattice decay \(e^{-\gamma_a n}\) is measured in time steps; with
physical time \(t=an\), its physical exponent is \(\gamma_a/a\).  Positivity
of every \(\gamma_a\) says nothing about a positive lower bound on
\(\gamma_a/a\) as \(a\downarrow0\).

Likewise, a finite-volume bound does not by itself identify the
infinite-volume Hilbert space, its vacuum, its local fields, or its
Hamiltonian.  Jaffe--Witten explicitly isolate uniform finite-volume control
and the \(T^4\to\mathbb R^4\) limit as missing work.

**Best salvage.** Either prove the common-exponent estimate directly for the
already-constructed continuum Schwinger functional, or prove regulator-uniform
physical-unit estimates plus an exact convergence theorem that preserves
the OS data, centered vectors, totality, and long-time bound.

### Critic 4 -- reflection positivity is not the whole reconstruction

Reflection positivity constructs a pre-Hilbert quotient in favorable
settings, but it does not alone establish all Wightman axioms, distribution
bounds, local fields, uniqueness, nontriviality, or the Clay short-distance
normalization.

**Best salvage.** State the precise corrected OS theorem being invoked and
verify every one of its hypotheses for the continuum limit.

### Critic 5 -- domain-free field notation

Pointlike quantum fields are operator-valued distributions and are generally
unbounded.  The expression \(A^*e^{-tH}A\) is not defined merely because it is
physically suggestive.

**Best salvage.** Work first with smeared fields on a proved common invariant
domain, with bounded local-algebra elements, or directly with OS equivalence
classes.  State the correlation-to-semigroup identity as a proved theorem.

### Critic 6 -- the endpoint

The decay exponent \(m\) does not exclude energy \(m\).

**Best salvage.** Conclude
\(\mathbf1_{[0,m)}(H)Q=0\), exactly as Theorem 2.1 does.  This is sufficient
for the Clay open interval \((0,m)\).  Do not claim
\(\mathbf1_{[0,m]}(H)Q=0\).

### Rebuilder

All six attacks leave the following implication intact:

\[
\begin{aligned}
&\text{complete continuum OS/Wightman Yang--Mills construction}\\
&+\ \text{OS-dense centered gauge-invariant family}\\
&+\ \text{one common positive connected autocorrelation exponent}\\
&\Longrightarrow
\mathbf1_{[0,m)}(H)(I-P_\Omega)=0\\
&\Longrightarrow\text{Clay mass gap on the reconstructed vacuum Hilbert space}.
\end{aligned}
\]

No quantitative frame lower bound and no summability condition belongs in
this minimal implication.

## 7. Smallest exact continuum certificate

For each compact simple \(G\), it is enough to provide the following finite
list of theorem-level objects and arrows.

### YM-C1 -- continuum existence/reconstruction

A nontrivial continuum Euclidean gauge-invariant theory on
\(\mathbb R^4\) satisfying a specified valid OS reconstruction theorem and the
additional Clay local-field and asymptotic-freedom requirements.

### YM-C2 -- semigroup identification

A reconstructed vacuum Hilbert space
\((\mathcal K_G,\Omega_G)\) and a proved strongly continuous semigroup

\[
T_G(t)=e^{-tH_G},\qquad H_G\ge0,\qquad H_G\Omega_G=0.
\]

### YM-C3 -- exact total family

A family \(F_i\) of gauge-invariant positive-time OS functionals for which

\[
v_i=[F_i]-\langle\Omega_G,[F_i]\rangle\Omega_G
\]

is defined and

\[
\overline{\operatorname{span}}\{v_i\}
 =\Omega_G^\perp.
\]

Taking an OS-defining dense family makes this a construction theorem rather
than an extra physical conjecture.

### YM-C4 -- common continuum exponent

One finite \(m_G>0\) such that for every \(i\) there exist finite
\(C_i,t_i\) with the exact connected diagonal identity and estimate

\[
\langle v_i,T_G(t)v_i\rangle
 =S_{i}^{\mathrm c}(t)
 \le C_i e^{-m_Gt}
 \qquad(t\ge t_i).
\]

Then Theorem 2.1 supplies the mass gap automatically.

This is the smallest surviving reconstruction target found in this audit.
The hard missing mathematics is YM-C1 and YM-C4.  YM-C2 and YM-C3 must still
be proved, but can be designed into a correct OS construction.  None is
established for four-dimensional continuum pure Yang--Mills in this packet.

## 8. Relation to the Lean firewall on this branch

The file
\(verification/ym-total-family/YMTotalFamilyFinite.lean\) proves a finite
detected-mode analogue using an explicit certificate time.  It verifies that
a positively detected finite mode obeying an all-time common exponential
bound cannot have energy below the exponent.

That Lean theorem is a sound finite firewall.  It does not formalize:

- the spectral theorem used in Theorem 2.1;
- OS reconstruction or a continuum Hamiltonian;
- the connected-correlator identity;
- Reeh--Schlieder or OS-defining totality;
- regulator-to-continuum convergence;
- any four-dimensional Yang--Mills construction;
- the official Clay theorem.

Encoding YM-C1--YM-C4 as assumptions would verify only the final transport,
not Yang--Mills.  A target-bound Lean development must construct and prove
those interfaces rather than hide them in custom axioms.

## 9. Provenance and status

This report refines the abstract theorem banked at:

- \(Stevemoraco/RH\), draft PR 71,
  \(showdown/millennium/runs/2026-08-13-v5/round-01-crosscut/ym-total-family/REPORT.md\);
- this branch's finite public verifier,
  \(verification/ym-total-family/YMTotalFamilyFinite.lean\).

It preserves the earlier correction: lower frame bounds and summable
prefactors are sufficient in some aggregate arguments but are not necessary
for the total-family/common-exponent theorem.

\[
\boxed{\text{Yang--Mills status: OPEN. Missing: YM-C1 through YM-C4, chiefly C1 and C4.}}
\]

\[
\boxed{\text{No six-alarm gate.}}
\]
