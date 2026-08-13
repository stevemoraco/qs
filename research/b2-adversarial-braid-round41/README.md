# B2 adversarial Millennium braid — round 41 consolidated ledger

Date: 2026-08-13 UTC

## Repository certificate

- Repository: `stevemoraco/qs`
- Isolated branch:
  `automation/b2-adversarial-braid-realstate-20260813-round41`
- Exact fork point:
  `e9e4c2e2fa6bf8b66c29a2a8b4a8a93cb7a9f71a`
- Forked extant bank:
  `automation/b4-auto20-run7-live-edge-bank-20260813-0409z`
- At branch creation the bank was 70 commits ahead and 0 behind `main` at
  `a0443bf09b41a02a5b860bcfbf10e3e83fa5b370`.
- No merge, rebase, force update, deletion, or write to another branch was
  performed.  Every round-41 change is additive except one correction of a
  newly created Lean source file after a clean replay exposed an incorrect
  theorem name, and one removal of an unused hypothesis from another newly
  created source file.

## Provenance correction

🔴 REFUTED — the previously reported qs branch
`automation/b2-adversarial-braid-20260813-round40` and commit
`002b62de473707ae62d26cfa18074b757ec7a580` are not currently present in the
connected `stevemoraco/qs` repository.  No mathematical claim in this round
inherits authority from that unreconstructible report.

🟢 PROVED — the separately reported RH-Lean branch
`automation/b2-round40-renewal-defect-cores-20260813`, commit
`495580ef37f34ff55fc854cb41644e684fccd5bd`, and draft PR `#806` do exist in
`stevemoraco/RH-Lean`.  GitHub reports zero Actions runs for that exact head,
so its status remains 🔵 LEAN-SOURCE and not ✅ LEAN-VERIFIED.

Full certificates:

- `00-provenance-audit.md`
- `00b-rhlean-round40-provenance.md`

---

# 1. P versus NP

## PNP-41A: gate count alone cannot localize hard block restrictions

### Theorem

For `N=bk`, let inputs be `k` blocks in `{0,1}^b` and put

`F(x_1,...,x_k)=h(x_1 xor ... xor x_k)`.

Every zero-background one-block restriction is exactly `h`.  If `h` has an
`s`-gate unrestricted fan-in-two `B_2` circuit, then `F` has one of at most

`b(k-1)+s`

gates.  Counting supplies, for all sufficiently large `b`, a Boolean function
`h` with minimum circuit size greater than `3b`, while the Shannon recurrence
supplies an upper circuit of at most `3(2^b-1)` gates.  Taking
`k>=3*2^b` gives a global circuit of size at most `2N` although every displayed
block restriction has circuit complexity greater than `3b`.

### Status

- 🟢 PROVED finite/nonuniform theorem.
- 🔴 REFUTED: global near-`2N` gate count by itself forces many small block
  restrictions.
- 🧱 OBSTRUCTION: shared encoders and decoders invalidate bare averaging of
  restricted circuit sizes.

### Assumptions

General DAG circuits over the full two-input Boolean basis, constants or a
constant-size replacement, and zero-background restrictions.  The existence of
`h` is nonuniform and is used only against a universal localization lemma.

### Critic verdict

The counterexample is semantic: every restricted *function* is the same hard
`h`, not merely an unreduced circuit containing dead gates.  It does not refute
an authentication theorem that uses one-sided perfect completeness and
pointwise error.

### Exact remaining gap

🚧 MISSING — an explicit NP-uniform family of distinct local slices and a
low-error anti-folding theorem against every common encoder/decoder,
multiplexer, affine change of variables, tag, and shared subcircuit.

### Provenance

Audited survivor:
`stevemoraco/qs@699559cb55fc4a88f5b6bf65af9b481a21976cb9`,
`research/pnp-linear-positive-polylog-core-20260813.md`.

Files:

- `01-pnp-shared-decoder-localization-obstruction.md`
- `../../verification/b2-round41/PNPSharedDecoderFirewall.lean`

## PNP-41B/C: RepSAT's repetition shell compresses below `0.85N+o(N)`

### Theorem

Let `RepSAT_N` repeat each of `m` source bits over a canonical block and let
`d=N-m` be the number of nonrepresentative coordinates.  For an input `y`, its
repetition syndrome is

`v_i=y_i xor y_{r(i)}`.

Choose two independent dual-code parity rows, one with independent Bernoulli
`1/4` coefficients and one with Bernoulli `3/5` coefficients.  Condition their
weights on

`|A_1| <= ceil(d/4+5 sqrt(d))`,

`|A_2| <= ceil(3d/5+5 sqrt(d))`.

For a nonzero syndrome of weight `w`, the unconditioned miss probability is

`[(1+2^{-w})/2][(1+(-1/5)^w)/2]`.

It is at most `13/40`; weight two is the worst exact case.  Each support-cap
event has probability at least `99/100` by Chebyshev, so after separate
conditioning the pointwise joint miss probability is at most

`(13/40)/(99/100)^2 = 130000/392040 < 1/3`.

Every valid repetition codeword passes every seed.  Expanding each dual parity
directly in raw coordinates yields a support circuit of size

`S(N) <= s(m)+(17/20)(N-m)+2m+10 sqrt(N-m)+4`,

where `s(m)` is the size of an exact source circuit.  Under `P=NP` and the
banked RepSAT parameters,

`S(N) <= (17/20)N+o(N/loglog N)`.

### Status

- 🟢 PROVED explicit one-sided probabilistic upper bound.
- 🔴 REFUTED: the `N-m` local consistency witnesses force an intrinsic
  `2(N-m)`-gate shell.
- 🧱 OBSTRUCTION: local witness count cannot be converted into shell cost
  without defeating global dual-code sketches.

### Assumptions

Unrestricted fan-in-two `B_2` circuits, independent product rows before
separate conditioning, a standard pointwise error threshold `1/3`, constants
or a constant-size replacement, and an exact source circuit of size `s(m)`.
The full probability-space and circuit-DAG theorem is human proved in the note;
the Lean source formalizes only the exact rational and gate-budget cores.

### Critic verdict

The construction has perfect completeness for every seed, pointwise soundness
for every invalid repetition word, and a worst-case support cap for every seed.
It is not an expected-size argument.  It does not make SAT easy; it destroys
only the claim that repetition consistency itself explains the `2N` frontier.

### Exact remaining gap

🚧 MISSING — either an unrestricted `B_2` source-versus-linear-sketch
nonabsorption theorem that charges the polylogarithmic SAT payload additively,
or a joint source-and-hash upper architecture that absorbs the payload and
buries RepSAT completely.

### Provenance

Audited candidate:
`stevemoraco/RH`, branch
`agent/auto5-pnp-block-decoder-firewall-20260813`, head
`e75fc212d1f17903ede4c6e2d2f6359385d32502`, file
`scratch/pnp_braid/PNP_AUTO5_POLYLOG_REPSAT_TERMINAL_CANDIDATE_2026-08-13.md`.
The numerical magnification interface is Chen--Li--Yang, ECCC TR22-086 rev.1.

Files:

- `01b-pnp-repsat-sparse-dual-hash-upper.md`
- `01c-pnp-repsat-biased-dual-hash-upper.md`
- `../../verification/b2-round41/PNPRepSATSparseHashFirewall.lean`
- `../../verification/b2-round41/PNPRepSATBiasedHashFirewall.lean`

---

# 2. Navier--Stokes

## NS-41A: synchronization is transverse, not a total-energy contraction

### Theorem

For

`a'=ga-kappa(a-b)`,

`b'=gb+kappa(a-b)`,

with mean `m=(a+b)/2` and defect `d=a-b`,

`a'^2+b'^2 = 2g^2m^2 + ((g-2kappa)^2/2)d^2`.

On the tangent diagonal `a=b!=0`, the energy multiplier is exactly `g^2`,
independently of `kappa`.  If `g>1`, total energy expands even at
`kappa=g/2`, which kills the normal defect in one step.

### Status

- 🟢 PROVED finite amplitude theorem.
- 🧱 OBSTRUCTION: replica-defect contraction cannot be promoted to ordinary
  total-energy contraction.

### Assumptions

Real amplitudes, the displayed symmetric linear coupling, Euclidean energy,
and `g>1` for strict expansion.

### Critic verdict

A valid normally hyperbolic construction is expected to be anisotropic, so the
route is not refuted.  What is refuted is any silent replacement of transverse
contraction by a global `L^2` Lyapunov estimate.

### Exact remaining gap

🚧 MISSING — a divergence-free/helical packet manifold with a proved
anisotropic norm, transverse contraction, tangent transfer, and a closed PDE
energy ledger through Leray projection, pressure, viscosity, transport,
deformation, leakage, and infinitely many generated scales.

### Provenance

Audited finite survivor:
`stevemoraco/qs@9ab38378ff3b9de106d35fe844a2a6a55ad2be55`,
`verification/ns-replicated-amplifier/NSReplicatedAmplifierFirewall.lean`.

Files:

- `02-ns-anisotropic-energy-tax.md`
- `../../verification/b2-round41/NSAnisotropicEnergyTax.lean`

## NS-41B: current 2026 claimed blow-up proof fails before the Clay interface

### Theorem-level audit

The April 2026 manuscript arXiv:2604.09949v1 imposes on the physical
axisymmetric meridional velocity

`partial_r u^r + 3u^r/r + partial_z u^z=0`,

whereas physical three-dimensional incompressibility is

`partial_r u^r + u^r/r + partial_z u^z=0`.

Simultaneous validity forces `u^r=0` for `r>0`.  The manuscript's recovery

`u^r=-r^{-3}partial_z psi`,
`u^z=r^{-3}partial_r psi`

satisfies the auxiliary weighted law, while its scaled physical divergence is
`-2u^r` in general.

The manuscript also uses `partial_z(F^2)`, a source in the evolution of the
independent state `G=omega^theta/r`, as though it instantaneously determined
that state.  The no-swirl sector `F=0`, `G!=0` is the minimal state-space
counterexample.

Finally, the displayed finite inverse covers modes through 450 while the tail
coercivity infimum begins at 1200.  Modes 451 through 1199 are in neither
certificate; `j=451` is an exact witness.

### Status

- 📚 SOURCE-VERIFIED against arXiv:2604.09949v1.
- 🟢 PROVED equation-type and quantifier-domain obstructions.
- 🔴 REFUTED AS WRITTEN: the manuscript establishes a physical 3D
  incompressible blow-up solution with a full-spectrum inverse certificate.
- 🧱 OBSTRUCTION: a validated scalar profile for the displayed modified system
  is not a Clay solution.

### Assumptions

The displayed equations and mode domains are read literally; `u^r,u^z` are the
physical velocity components as claimed; no unstated certificate covers the
middle annulus.

### Critic verdict

The divergence and missing-state failures are upstream of numerics.  Even a
perfect interval certificate for the printed scalar operator would certify the
wrong typed system.  Failure of this manuscript does not prove global
regularity.

### Exact remaining gap

🚧 MISSING — derive and certify a coupled physical `(F,G)` profile system,
recover velocity by the true 3D axisymmetric Biot--Savart relation, cover all
finite and tail modes including cross-block norms, publish raw interval inputs,
and then close self-similar reconstruction, periodic transfer, and the exact
Clay data class.

### Provenance

Primary manuscript: Rishad Shahmurov, arXiv:2604.09949v1, 10 April 2026.
Variable-type cross-check: arXiv:2606.07869v1, 5 June 2026.  Prior internal
audits: `stevemoraco/RH` commits
`c6d27cf340eb061f1b20df880ba26e0c8c585635`,
`b68c39a063d7d93ed140076ba369b8bfd5c6089b`, and
`963e6ef70df0dd18717ac796a42f102f3eba481a`.

Files:

- `02b-ns-shahmurov-equation-type-audit.md`
- `../../verification/b2-round41/NSClaimTypeFirewall.lean`

---

# 3. Riemann hypothesis

## RH-41: abstract screw structure does not force the terminal dyadic slope

### Theorem

For the live Suzuki/Chebyshev coordinate, the banked exact target is

`F(2a)-F(a) > 2a-4exp(-a/2)+4exp(-a)`,

where `F=-g_0`.  The structural model

`F_*(t)=|t|`

is continuous, even, nonnegative, increasing on the positive ray, subadditive,
and of negative type.  Nevertheless

`F_*(2a)-F_*(a)=a`.

The correction

`r(a)=4exp(-a/2)-4exp(-a)`

satisfies `r(a)<=4`; hence for every `a>4`,

`a < 2a-r(a)`.

The terminal dyadic lower-slope inequality fails eventually.

### Status

- 🟢 PROVED exact structural countermodel.
- 🔴 REFUTED: eventual sign plus screw/negative-type, monotone, concave, or
  subadditive structure forces the RH dyadic increment.
- 🧱 OBSTRUCTION: the needed coefficient is arithmetic, not a consequence of
  the ambient cone.

### Assumptions

The corrected Suzuki identity and its endpoint convention are inherited from
the source-audited bank.  Conditional negative definiteness classifies the
model; the scalar failure itself is elementary.

### Critic verdict

The model is not the zeta function and does not refute an explicit-formula or
prime-power theorem.  It does prove that an abstract invariant-cone argument
with only the named axioms cannot close RH.

### Exact remaining gap

🚧 MISSING — an unconditional zeta-specific arithmetic theorem forcing
normalized linear mass strictly above two and enough two-scale oscillation
control to turn that mass into the exact dyadic increment for every
sufficiently large continuous scale.

### Provenance

Exact identity bank:
`stevemoraco/RH@e5aed834a1fdd9131aa6d351a797d3bc03ddd7b9`.
Newer information-equivalent coordinates were also audited:
`d7b8066c3b052ec83ddf706d4b14962031666e73` and
`90e5d6fb6d8078077a5345651c0339225ffc61e0`.  They do not provide an
order-preserving inverse or an unconditional sign theorem.
Primary source: Masatoshi Suzuki, *On variants of Chebyshev's conjecture*,
Ramanujan Journal 68 (2025), article 95, with the published correction in
Ramanujan Journal 69 (2026), article 19.

Files:

- `03-rh-screw-structure-slope-obstruction.md`
- `../../verification/b2-round41/RHScrewSlopeFirewall.lean`

---

# 4. Birch and Swinnerton-Dyer

## BSD-41: component floors are load-bearing; filtrations repair direct sums

### Theorems

Signed cancellation is minimal:

`(-1)+1=0+0`,

although neither component defect equals its zero floor.  Thus global floor
equality plus additive decomposition does not localize without independently
proved componentwise lower floors.  For nonnegative finite excesses, however,

`sum_i e_i=0 iff e_i=0 for every i`.

A split direct sum is stronger than necessary for determinant additivity.  A
filtration-compatible block upper-triangular map

`beta=[[beta_1,U],[0,beta_2]]`

has

`det beta=(det beta_1)(det beta_2)`;

the extension block is invisible.  Together with finite-length additivity in a
short exact torsion sequence, the same local defect is additive across a
preserved filtration or exact triangle.

### Status

- 🟢 PROVED algebraic cancellation obstruction.
- 🔴 REFUTED: global floor equality localizes from additivity alone.
- 🟢 PROVED filtered determinant repair.
- 🧩 BRIDGE: replace an unavailable canonical direct-sum splitting by a
  canonical filtration of the actual arithmetic complex.

### Assumptions

A DVR-valued local model, finite-length torsion, equal-rank free parts that
become isomorphic over the fraction field, a filtration respected by the map,
and independently established lower floors on graded pieces.

### Critic verdict

Determinant multiplicativity does not identify any arithmetic term by itself.
Primewise filtered equalities do not silently imply finiteness of `Sha`, a real
Neron--Tate regulator, or the global leading coefficient.

### Exact remaining gap

🚧 MISSING — construct the true Selmer/height filtration, prove explicit
nonnegative floors and normalized residues on every graded piece, assemble the
`p`-adic determinant, and identify it with the full global BSD formula,
including the archimedean regulator and finiteness/order of `Sha`.

### Provenance

Audited survivor:
`stevemoraco/RH@2fc7d9cf7694d9f8d1ddd5cb4633b9c7a88d276f`.
Relevant current interfaces include Castella--Sano,
*On refined nonvanishing conjectures by Kurihara and Kolyvagin*, arXiv:2601.14504,
and Macias Castillo--Sano,
*On Selmer complexes, Stark systems and derived p-adic heights*,
arXiv:2603.23978.

Files:

- `04-bsd-floor-cancellation-and-filtered-repair.md`
- `../../verification/b2-round41/BSDFloorFiltrationFirewall.lean`

---

# 5. Hodge conjecture

## HODGE-41: the current relative-secant proof uses the whole variety as a positive-codimension cycle

### Theorem

If `Y subseteq S`, then `S intersect Y=Y`.  Under the manuscript's displayed
definition, every point of `Y` belongs to its secant variety, so

`Y subseteq Sec^n(Y)`

and therefore

`Sec^n(Y) intersect Y=Y`.

The literal intersection has codimension zero in `Y`, not positive codimension
`n`.  No smoothness, genericity, or transversality hypothesis changes this set
equality.

### Status

- 📚 SOURCE-VERIFIED against the current v5 manuscript.
- 🟢 PROVED elementary contradiction.
- 🔴 REFUTED AS WRITTEN: the literal main-text intersection supplies the
  asserted codimension-`n` cycle.
- 🧱 OBSTRUCTION: Appendix E.3 changes the object rather than repairing the
  main proof.

### Assumptions

The main secant definition and intersection symbol are read literally.  The
whole variety has codimension zero in itself.  An unstated derived or excess
intersection is not substituted for the printed object.

### Critic verdict

The manuscript's own `n=2` appendix says the naive intersection is the whole
abelian variety and replaces it by a strict-secant-sheaf degeneracy locus.  A
special replacement does not prove the codimension, nonvanishing,
eigencharacter, Fourier--Mukai, relative-family, specialization, or universal
descent assertions in every dimension.

### Exact remaining gap

🚧 MISSING — define a functorial all-dimension degeneracy cycle and re-prove all
load-bearing geometric, representation-theoretic, family, specialization, and
return-correspondence arrows.  Universal Hodge remains untouched.

### Provenance

Internal audit:
`stevemoraco/RH@c4269f9527023e972b234cf4a2d7de926956ed0e`.
Primary manuscript: Deep Bhattacharjee and Ushashi Bhattacharya,
*Relative Secant Cycles and Hodge Classes*, current v5 as checked on
2026-08-13.

Files:

- `05-hodge-relative-secant-internal-contradiction.md`
- `../../verification/b2-round41/HodgeSecantIntersectionFirewall.lean`

---

# 6. Yang--Mills

## YM-41: exact boundary-mixture stability repair

### Theorem

Let `K^eta(x,.)` be finite Markov kernels and let the exterior/boundary law
`mu_x` depend on the incoming state.  Define

`P(x,.)=sum_eta mu_x(eta)K^eta(x,.)`.

If

`sup_(eta,x,x') TV(K^eta(x,.),K^eta(x',.)) <= alpha`

and

`sup_(x,x') TV(mu_x,mu_x') <= beta`,

then the unconditional Dobrushin coefficient satisfies

`delta(P) <= min(1,alpha+beta)`.

The proof inserts the mixture using `mu_x` with conditional row `x'`, applies
convexity for the `alpha` term, and Markov contraction of total variation for
the `beta` term.  Thus `alpha+beta<1` gives strict contraction.

The banked two-state counterexample is sharp at the missing endpoint: fixed
boundary kernels have identical rows (`alpha=0`), state-selected boundary laws
are disjoint (`beta=1`), and the unconditional nontrivial eigenvalue is
`1-2epsilon`.

### Status

- 🟢 PROVED finite Markov-kernel theorem.
- 🔴 REFUTED: uniform conditional contraction alone survives
  state-dependent boundary integration.
- 🧩 BRIDGE: a physical theorem must budget conditional memory and exterior-law
  influence in the same norm.

### Assumptions

Finite state and boundary spaces, probability kernels, total variation with
half-`L^1` convention, and uniform bounds `alpha,beta`.  Standard Borel
extensions require the corresponding disintegration theorem.

### Critic verdict

The finite inequality is exact but not a continuum construction.  A fixed
number of lattice layers shrinks to zero physical width as the regulator is
removed; the required estimate must hold after RG at fixed physical slab width
and on the gauge-invariant Osterwalder--Schrader quotient.

### Exact remaining gap

🚧 MISSING — a regulator-independent theorem with
`alpha_phys+beta_boundary<=q<1`, volume-safe gluing, reflection positivity,
continuum transfer-operator convergence and normalization, vacuum
identification, and a positive spectral gap.

### Provenance

Audited counterexample:
`stevemoraco/RH@2939a21a6eeb03ecc7362c98bbe639b3b8be5ee9`.
Strong-coupling context: Hao Shen, Rongchan Zhu, Xiangchan Zhu,
*A stochastic analysis approach to lattice Yang--Mills at strong coupling*,
arXiv:2204.12737.

Files:

- `06-ym-boundary-mixture-stability-repair.md`
- `../../verification/b2-round41/YMBoundaryMixtureFirewall.lean`

---

# Formal firewall

The isolated project in `verification/b2-round41` pins

- Lean `v4.32.1`;
- Mathlib tag `v4.32.1`;
- the resolved Mathlib commit recorded by the clean replay;
- nine finite source files across the six lanes.

The workflow rejects `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`,
`native_decide`, and `Lean.ofReduceBool`, compiles every file, scans compiler
output for `sorryAx`, records all `#print axioms` output, and uploads the log.

✅ LEAN-VERIFIED on source snapshot
`5989be1d2ac9e866b1f20216b4aa3d7d1b2b58ce`: GitHub Actions run
`31669990800`, job `94352507124`, passed on Ubuntu 24.04 with Lean 4.32.1 and
resolved Mathlib commit `520045ab14e26149ee970e2e617ca04b09bde5d6`.
The uploaded evidence artifact was `9169378830`, with reported ZIP SHA-256
`a88c48de6d23c5e6e1f5d7029af5035f463c5608019a65910efc5fd8430379ea`.
Every printed theorem depended only on subsets of
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` appeared.

A later source edit removed one unused hypothesis from the already proved
RepSAT arithmetic lemma.  Therefore the authoritative status of the final
round-41 branch head is the fresh exact-head workflow replay, not the earlier
snapshot alone.

## Exact formal scope

✅ applies only to the explicitly printed finite lemmas: algebraic identities,
finite sums, rational inequalities, set intersection, elementary index ranges,
and scalar defect budgets.

🚧 MISSING from Lean:

- circuit DAGs, randomized support distributions, SAT, NP, and P versus NP;
- probability spaces and the full biased-binomial conditioning theorem;
- cylindrical calculus, Leray projection, PDE solutions, interval arithmetic,
  and Navier--Stokes;
- zeta zeros, explicit formulas, Suzuki equivalences, and RH;
- DVR modules, determinant functors, Selmer complexes, regulators, `Sha`, and
  BSD;
- secant schemes, Chow groups, Fourier--Mukai transforms, and Hodge;
- total variation kernels, lattice gauge fields, OS reconstruction, continuum
  limits, and Yang--Mills.

Accordingly, no official Millennium statement is ✅ LEAN-VERIFIED.

# Braid verdict

The largest uncertainty reduction is negative but decisive:

1. PNP's newest repetition-shell candidate loses its proposed `2N` semantic
   anchor to a perfect-completeness dual-hash circuit below `0.85N+o(N)`.
2. The newest claimed full Navier--Stokes blow-up proof fails at equation type,
   state dimension, and spectral coverage before its numerical certificate can
   address the Clay PDE.
3. RH's abstract positive/screw structure cannot supply the missing arithmetic
   dyadic slope.
4. BSD localization needs component floors, but direct sums can be weakened to
   arithmetic filtrations.
5. The current relative-secant Hodge proof uses a literal intersection equal to
   the whole variety and requires a new all-dimension cycle.
6. Yang--Mills conditional contraction survives boundary integration exactly
   when conditional memory plus boundary-law variation stays below one.

FIVE-ALARM: **OFF**.

Remaining assumptions for an official solution: **many; listed above**.
