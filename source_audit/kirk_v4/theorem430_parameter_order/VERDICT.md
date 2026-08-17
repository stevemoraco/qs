# Kirk v4 Theorem 4.30 parameter-order audit

Date: 2026-08-16

Status: **source/dependency closure · apparent cutoff circularity retired after type split · analytic truth not independently verified · no Yang–Mills or Clay proof · FIVE-ALARM OFF**

## Hostile question

Theorem 4.30 defines

```text
Gamma = log_2(max_m K_m) + epsilon
```

and then chooses the engineering cutoff `D` so that

```text
delta_D > Gamma + 2.
```

A genuine circularity would occur if the one-step supplier constants were `K_m(D)`: pointwise finiteness of every `K_m(D)` and `delta_D -> infinity` do not imply that any `D` satisfies

```text
delta_D > log_2 K_m(D) + 2.
```

The manuscript also has localization constants `C_D,p_D`, so the parameter types had to be reconstructed exactly.

## Immutable source and replays

Pinned source: Kirk v4, Zenodo record `21765806`.

PDF SHA-256:

```text
c78a3ce6d273ce7e2d32ecd2cf796a81d1f16160aadc3231752c9dbf65a6befa
```

Focused constant-origin replay:

```text
source branch    verification/ym-kirk-v4-section7-extract-20260816-gpt56pro
commit           fdef042c1d3ca7c20f837f2ec72825d5960631ce
run/job          31981093845 / 95247881698
conclusion       success
artifact         9272353988
artifact digest  sha256:1855c45e44bfed0f01461baab2da579f38c8e122383f55e3e6bbb20813ec46e1
```

Focused extraction/projector replay:

```text
source branch    verification/ym-kirk-v4-section7-extract-20260816-gpt56pro
commit           c3646a10e1acee7f2985e748823a3d065cad86b1
run/job          31981306854 / 95248443814
conclusion       success
artifact         9272412794
artifact digest  sha256:91d65e79f36971d2c1a17096c7b17abdba20a9799615178fdb31bbad6a7807c1
```

Fresh local downloads matched both GitHub artifact digests exactly.

## Resolution: two different projectors

The apparent circularity comes from conflating two finite-dimensional operations.

### 1. Fixed one-step extraction

Section 4.4 fixes the actual one-step RG coordinate split before any auxiliary macrostep cutoff is chosen:

- `Pi_ext` extracts vacuum, tangent-normalized Yang–Mills, declared marked/contact jets below degree five, and the declared redundant/odd sectors;
- `Pi_irr = I - Pi_ext` is placed on the **fixed jet truncation through degree eight**;
- the displayed stable one-step fiber is

```text
J_st = J_5 + J_6 + J_7 + J_8.
```

Theorem 4.17 proves the one-step Gaussian/Wick stable matrix on this fixed finite fiber. Its entries come from one fixed forty-nine-path cell and fixed Wick conversion.

Section 4.6 then defines the six modules of the exact normalized one-step map. Its theorem statements have no auxiliary `D` argument. Theorem 4.29 supplies `K_m`, through structural order three and arbitrary fixed passive-source order, for this fixed scale-two map. The one-step local module is therefore the declared fixed extraction module of Section 4.4, not the later arbitrary macrostep projector.

This is also reflected in the notation:

```text
K_m^loc
```

is one fixed one-step module constant, while the arbitrary cutoff constants below are explicitly indexed by `D`.

### 2. Arbitrary macrostep analysis projector

Only after the fixed one-step map has been established does Section 4.5 fix a finite dyadic macrostep `L=2^s` and introduce

```text
Loc_{D,Y} : F_Y -> J_D(Y).
```

Lemma 4.20 assigns this auxiliary projector the explicitly cutoff-dependent constants

```text
C_D (1 + tau(Y))^{p_D}
```

and the Taylor-remainder gain

```text
L^{3-D}.
```

Theorem 4.22 carries exactly these `C_D,p_D` constants into the short nonlocal macrostep row. They are chosen only after the complete macrostep envelope has been bounded.

## Correct parameter order

The source-native order is therefore

```text
fixed group/representation/source order
  -> fixed Section-4.4 one-step extraction
  -> one-step constants K_m
  -> Gamma = log_2(max K_m) + epsilon
  -> choose auxiliary macrostep cutoff D with D-3 > Gamma+2
  -> fix C_D,p_D
  -> choose finite dyadic L large enough
  -> extend the finite local equivalent norm to the rooted space.
```

The `D`-dependence of `C_D,p_D` is harmless because `D` is fixed before `L -> large`; these constants affect only the prefactor and logarithmic power. The exponent is

```text
Gamma - (D-3) < -2.
```

Thus Theorem 4.30 does not require any unsupported conclusion of the form `delta_D` beats an arbitrary `Gamma(D)`.

## Why the source was easy to misread

Section 4.5, which defines the arbitrary `Loc_D`, appears before Section 4.6, which packages the normalized one-step modules. Lemma 4.28 also says “the localization projector” without restating that the one-step module uses the already declared fixed extraction. Read in isolation, that phrase can make `K_m^loc` look like a `D`-dependent macrostep constant.

The type reconstruction resolves the ambiguity:

- the arbitrary projector is always written `Loc_D`, `Pi_D`, `C_D`, or `p_D` and belongs to the macrostep split;
- Theorem 4.29's one-step map has no `D` parameter and follows the fixed Section-4.4 degree-eight coordinate split;
- Theorem 4.30 explicitly says to fix finite `Gamma` before choosing `D`.

A source rewrite should rename the fixed module `K_m^ext` and reserve `Loc_D` for the macrostep analysis projector.

## INVENTOR -> CRITIC -> REWRITER

### INVENTOR

Separate the RG coordinate extraction from the auxiliary macrostep Taylor cutoff. Compose the fixed exact scale-two map first, obtaining a macrostep envelope with exponent `Gamma` independent of the later cutoff. Apply `Loc_D` only to the collected macrostep output and choose `D` to beat that fixed exponent.

### CRITIC

This is a source/dependency closure, not an independent analytic proof. It still assumes that Theorems 4.17, 4.29, and the macrostep composition really hold in the stated root-marked spaces with one fixed support exponent and common weak ball. It also assumes the one-step E4 operation is exactly the fixed declared extraction rather than an unprinted all-degree projector.

The generic quantifier firewall remains valid: if an implementation replaces the fixed one-step extraction by `Loc_D` at every scale, or lets its supplier constants depend on the later auxiliary cutoff, then pointwise finiteness is insufficient and a growth theorem such as

```text
log K(D) = o(D)
```

would be required.

### REWRITER

Retire the source-level gate

```text
YM-KIRK-430-JET-CUTOFF-SUPPLIER-CIRCULARITY
```

under the explicit two-projector typing above.

The next analytic target remains

```text
YM-KIRK-527-U5-COMPLETE-PACKET-ANALYTIC-REPLAY
```

with an additional audit requirement: the replay must keep the fixed one-step extraction and the later auxiliary macrostep `Loc_D` as distinct maps and must verify that the former's constants are independent of the latter's cutoff.

## Boundary

No new Lean declaration is claimed. Existing finite Lean firewalls remain relevant to any alternative proof with cutoff-dependent supplier exponents.

This audit does not verify the one-step analytic module bounds, the arbitrary macrostep localization theorem, Theorem 4.30 analytically, Theorem 5.27(U5), the multiscale continuum construction, Osterwalder–Schrader reconstruction, a physical mass gap, nontriviality, or the Clay theorem.

FIVE-ALARM OFF.
