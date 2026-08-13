# Hodge B1 — trigonal branch collision forces target-base degree at least three

Date: 2026-08-13

Status: 🟢 PROVED abstract geometric degree firewall · 🧱 OBSTRUCTION · 🧩 BRIDGE · 🔵 LEAN-SOURCE: NO NEW SOURCE · ✅ LEAN-VERIFIED: NO NEW CLAIM · 🚧 higher-degree/non-graph cases remain.

Provenance:

- `stevemoraco/qs@540178dd48322d0c3fe42f58e5bc606566beb63f` — first genus-10 trigonal obstruction;
- `stevemoraco/qs@1bd80c13c547b70af4985826f0886dcc026c5c8d` — repaired deck-fixed-locus argument;
- `stevemoraco/qs@3b392990386dc26150db96f4856bf8c2c1db3edb` — strengthened finite Lean arithmetic core.

The parent kills the first `F_4`, `NS(Y)=U`, `L^2=8` graph layer because a general source ruling fibre contains three moving-branch points whose target ruling values are forced equal, while the target ruling has degree one on the image curve. The same argument is not degree-one-specific.

## INVENTOR — retain the fibre length instead of specializing it to one

Let `C` be the moving source branch curve and suppose:

1. `pi_s : C -> P^1` is a trigonal morphism;
2. the relevant genus/degree argument makes this trigonal pencil unique up to `PGL_2`;
3. deck equivariance sends the generic moving source branch into the moving target branch, producing an isomorphism `alpha : C -> C_t` as in the repaired parent;
4. hence there is `tau in PGL_2` with

   `pi_t o alpha = tau o pi_s`;

5. for a general source ruling fibre `F_u ~= P^1`, the descended graph map is defined at the three distinct branch points

   `x_1,x_2,x_3 in C intersect F_u`;

6. the composite target-base map

   `phi_u := pi_t o q|_{F_u} : P^1 -> P^1`

   is nonconstant of degree `d`.

The trigonal identity gives

`phi_u(x_1)=phi_u(x_2)=phi_u(x_3)=tau(u)`.                           (1)

A nonconstant morphism `P^1 -> P^1` of degree `d` has every fibre of scheme length `d`. In particular, a fibre cannot contain more than `d` distinct points. Therefore (1) forces

`boxed: d >= 3`.                                                     (2)

So every graph realization satisfying the parent branch-identification mechanism and having target-base degree one **or two** is impossible.

## Variant with two degrees visible

Suppose more generally that on a general ruling fibre

`F_u --q--> D_u --pi_t--> P^1`

has degrees

`deg(q|_{F_u})=e`,

`deg(pi_t|_{D_u})=m`.

Then, whenever neither map contracts the general fibre and the maps extend on the normalizations,

`deg(phi_u)=e m`.

The same three-point collision therefore gives

`boxed: e m >= 3`.                                                   (3)

Thus any proposed graph layer with `e m <= 2` is dead before any Hodge-cycle computation.

The banked `L^2=8` layer is the special case `e=m=1`.

## CRITIC

This theorem does **not** classify all higher `F_4` or `U(13)` layers. It applies only after the parent geometric bridges have been proved for the layer under consideration:

- deck-equivariant branch preservation;
- noncontraction of the moving branch;
- the genus/isomorphism step;
- uniqueness of the trigonal pencil;
- well-definedness at the three general branch points;
- the claimed fibre degrees on normalizations.

If the target branch map is not isomorphic to the source branch, if the graph map has a higher-degree restriction, or if the construction is a relative cycle/correspondence rather than a graph, the argument does not apply.

The phrase “degree two” also cannot be replaced by a set-theoretic generic-injectivity slogan. The correct invariant is scheme-theoretic fibre length of the morphism on the normalization.

## REWRITER — screen the entire graph search by one integer before solving equations

Before performing any rational-square, secant, Hilbert–Burch, or correspondence computation for another graph layer, compute the single integer

`d = deg(pi_t o q|_{F_u})`.

If `d<3`, stop: the trigonal branch identity already contradicts the fibre degree.

Only graph layers with

`d >= 3`

need further arithmetic or geometry. This is a strict search-space reduction: the first obstruction is now a degree threshold, not the specific class `s+4f`.

### Exact remaining gap

Inventory every hostile-surviving `F_4`/`U` and `U(13)` graph layer and compute its normalized general-fibre target-base degree. Eliminate all `d<3` layers immediately. For the first `d>=3` survivor, test whether ramification, deck-fixed loci, or higher-gonal uniqueness supplies the next obstruction. The independent non-graph/relative-cycle route remains untouched.

### Lean status

No new Lean file is added. The existing source at `3b392990386dc26150db96f4856bf8c2c1db3edb` already verifies the genus-10 arithmetic, the `3 x 3` Castelnuovo–Severi numerical ceiling, and the final finite injectivity collision. Formalizing “a degree-`d` morphism of projective lines has fibre length `d`” would require the actual algebraic-geometry degree interface; a detached finite pigeonhole shadow would not close the geometric bridge and is therefore not promoted.

Critic verdict: 🟢 exact once the parent branch-identification hypotheses and fibre degree are instantiated; 🧱 kills every subtrigonal graph layer; 🚧 does not touch degree >=3 or non-graph constructions.

FIVE-ALARM: OFF.