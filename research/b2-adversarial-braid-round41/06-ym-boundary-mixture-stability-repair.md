# Yang--Mills: exact boundary-mixture stability theorem for conditional contraction

Date: 2026-08-13

## Status

🟢 PROVED finite Markov-kernel theorem.

🧩 BRIDGE repairing the newest boundary-mixture obstruction at its exact norm.

🧱 OBSTRUCTION remains at the gauge-invariant continuum interface.

No Yang--Mills construction or mass-gap theorem is claimed.

## Audited survivor

The newest dedicated Yang--Mills branch gives a two-state counterexample in
which every boundary-conditioned kernel has identical rows and therefore
perfect one-step contraction, but the boundary label is selected from the
incoming state.  The unconditional kernel then has nontrivial eigenvalue
`1-2 epsilon`, so its gap tends to zero as `epsilon -> 0`.

That counterexample is correct.  It identifies boundary-law dependence as an
independent defect.  The next question is whether a sharp sufficient theorem
can be stated without guessing a large analytic framework.

## Exact theorem

Let `X` and `E` be finite sets.  For each boundary label `eta in E`, let
`K^eta(x,.)` be a Markov kernel on `X`.  For each incoming state `x`, let
`mu_x` be a probability law on `E`.  Define the state-dependent mixture

`P(x,.) = sum_eta mu_x(eta) K^eta(x,.)`.

Use total variation distance with the convention

`TV(p,q) = (1/2) sum_z |p(z)-q(z)|`.

Assume

`sup_(eta,x,x') TV(K^eta(x,.),K^eta(x',.)) <= alpha`

and

`sup_(x,x') TV(mu_x,mu_x') <= beta`.

Then the Dobrushin coefficient of the unconditional kernel satisfies

`boxed: delta(P) <= min(1, alpha+beta).`

In particular, if

`alpha+beta < 1`,

then `P` is a strict one-step contraction in total variation.

### Proof

Fix `x,x'`.  Insert the intermediate distribution using the boundary weights
`mu_x` but the conditional rows at `x'`:

`Q(.) = sum_eta mu_x(eta) K^eta(x',.)`.

The triangle inequality gives

`TV(P(x,.),P(x',.))
 <= TV(P(x,.),Q)+TV(Q,P(x',.)).`

For the first term, convexity of total variation gives

`TV(P(x,.),Q)
 <= sum_eta mu_x(eta)
       TV(K^eta(x,.),K^eta(x',.))
 <= alpha.`

For the second term, the map sending a boundary law `nu` to

`sum_eta nu(eta) K^eta(x',.)`

is a Markov kernel and therefore contracts total variation.  Hence

`TV(Q,P(x',.)) <= TV(mu_x,mu_x') <= beta.`

Taking the supremum proves `delta(P)<=alpha+beta`; every total variation
distance is at most one.

## Sharpness against the banked counterexample

In the two-state construction, every fixed-boundary kernel has identical rows,
so `alpha=0`.  The deterministic boundary laws for the two incoming states are
disjoint, so `beta=1`.  The theorem then gives only `delta(P)<=1`, exactly the
point at which strict contraction is lost.  Thus the missing boundary term is
not an artifact of the proof.

For the displayed unconditional matrix

`[[1-epsilon,epsilon],[epsilon,1-epsilon]]`,

the exact Dobrushin coefficient and the modulus of the nontrivial eigenvalue
are both `1-2epsilon`.  The counterexample approaches the boundary
`alpha+beta=1` while the spectral gap collapses.

## Claim + counterexample + salvage

### Claimant

Uniform projective or cone contraction for every physical slab conditioned on
its exterior should yield a global transfer gap after integrating out that
exterior.

### Critic

False without boundary stability.  The banked two-state model has perfect
conditional contraction and arbitrarily poor unconditional contraction.

### Rebuilder

The corrected local theorem has two independent budgets:

1. conditional kernel memory, measured by `alpha` or a projective analogue;
2. incoming-state sensitivity of the exterior law, measured by `beta` or a
   likelihood-ratio/Dobrushin norm.

🧩 BRIDGE — prove a regulator-independent inequality

`alpha_phys + beta_boundary <= q < 1`

on the same gauge-invariant, Osterwalder--Schrader-positive physical slab and
at a fixed physical width.  Then transfer contraction can survive boundary
integration.  A projective-cone version may replace TV, but it must retain an
explicit additive or multiplicative boundary defect budget.

## Scale/type check

- The theorem is finite probability theory.
- A lattice spacing `a` and a fixed number of lattice steps are not a fixed
  physical slab; the number of steps must diverge as `a -> 0` unless an RG
  theorem has already produced a physical-scale kernel.
- Strict Markov contraction does not by itself construct the Euclidean field,
  prove reflection positivity, identify the vacuum sector, or normalize the
  Hamiltonian.
- A dimensionless contraction `q<1` at physical time `tau` gives the formal
  energy scale `-log(q)/tau` only after the OS transfer operator and quotient
  have been rigorously identified.
- Strong-coupling lattice mass-gap results occur in a controlled regulator
  regime; they do not by themselves produce the four-dimensional continuum
  theory required by Clay.

## Assumptions

- Finite state and boundary spaces; the same proof extends to standard Borel
  spaces when disintegration and TV contraction are available.
- Each `K^eta` and `mu_x` is a probability law.
- Uniform conditional Dobrushin coefficient `alpha` and uniform boundary-law
  variation `beta`.
- The strict conclusion requires `alpha+beta<1`.

## Critic verdict

🟢 PROVED as the exact finite repair.

🔴 REFUTED: conditional contraction alone is enough.

🟡 CONDITIONAL for Yang--Mills: a gauge-invariant physical-slab analogue with
uniform boundary control remains unproved.

## Lean status

- 🔵 LEAN-SOURCE:
  `verification/b2-round41/YMBoundaryMixtureFirewall.lean` stages the scalar
  defect-budget theorem and the exact two-state eigenmode calculation.
- ✅ LEAN-VERIFIED: NO; total variation, projective cones, gauge fields, OS
  reconstruction, and the continuum limit are not formalized there.

## Exact remaining gap

🚧 MISSING — for a regulator sequence defining nontrivial four-dimensional
compact-gauge Yang--Mills, prove at fixed physical slab width on the
OS/gauge-invariant quotient:

- uniform conditional cone contraction;
- uniform exterior-law influence control;
- a combined contraction margin below one;
- volume-safe gluing and reflection positivity;
- convergence and normalization of the continuum transfer operator;
- a positive spectral gap above the vacuum.

## Provenance

- Internal obstruction: `stevemoraco/RH` branch
  `agent/b1-ym-boundary-mixture-counterexample-20260813-run28`, commit
  `2939a21a6eeb03ecc7362c98bbe639b3b8be5ee9`.
- Strong-coupling lattice context: Hao Shen, Rongchan Zhu, Xiangchan Zhu,
  *A stochastic analysis approach to lattice Yang--Mills at strong coupling*,
  arXiv:2204.12737.
- Official scope: Clay/Jaffe--Witten Yang--Mills existence and mass-gap problem.
