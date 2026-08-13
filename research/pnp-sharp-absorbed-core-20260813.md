# Sharp absorbed-core transfer

Date: 2026-08-13
Base: `agent/gpt56-pnp-hidden-seed-absorption-20260813-run1` at `ead634df24468aa2539b0e3cf7c9f90224f39211`.
Status: finite theorem only; no NP-uniform construction and no P-vs-NP conclusion.

## Theorem

Let `T` be a global positive set, let `P subset T` be a local positive slice, and let `h=(h_1,...,h_M)` be a list of core points; repetitions are allowed. For a set `B`, write

`N_h(B)=|{j:h_j in B}|`.

Assume every permitted acceptance set `A` satisfying `P subset A` obeys

`N_h(A) >= rho M`.

Put `q=N_h(T)` and `a=q/M`, and assume `q<rho M`. For each global negative point `x`, let `m_h(x)` be its multiplicity in `h` and assign

`w(x)=m_h(x)/(rho M-q)`.

Every permitted `A` accepting all of `T` has weight at least one on `A\T`, while the total weight is exactly

`(M-q)/(rho M-q)=(1-a)/(rho-a)`.

Hence

`tau_f <= (1-a)/(rho-a)`.

## Proof

A global acceptance set contains `P`, so it accepts at least `rho M` core incidences. Exactly `q` core incidences lie in `T`, and all of them are accepted. Therefore at least `rho M-q` accepted incidences lie in `A\T`. Double counting these incidences gives edge weight at least one. The total multiplicity outside `T` is exactly `M-q`, proving the displayed total mass.

This corrects the parent bound `1/(rho-a)`, which used only the coarse estimate that residual multiplicity is at most `M`.

At `rho=1/4` and `a<=1/8`, the sharp bound is

`tau_f <= 7`,

not merely `8`. More generally

`(1-a)/(1/4-a)=4+12a/(1-4a)`.

If the core list is internally distinct, every residual incidence is a distinct false positive, so a circuit accepting `T` has at least `rho M-q` distinct semantic witnesses in the fixed core, with congestion one.

## Aggregate families collapse to one surviving core

Suppose cores have sizes `M_s`, absorbed counts `q_s`, and the same local density `rho`. If

`a=(sum_s q_s)/(sum_s M_s)<rho`,

then some seed has `a_s=q_s/M_s<=a`. The function

`f_rho(x)=(1-x)/(rho-x)`

is increasing for `x<rho<=1`, because its derivative is `(1-rho)/(rho-x)^2`. Applying the one-core theorem to that seed gives

`tau_f<=f_rho(a_s)<=f_rho(a)`.

Thus aggregate multiplicity weighting is convenient bookkeeping but is never quantitatively better than the best local core. The best seed is an analysis witness; an NP verifier does not need to identify it.

## Consequence for the research target

For fractional hardness, neither hardness of every admitted seed nor bounded overlap among all local cores is necessary. It is enough that the global sparse language contain one locally hard slice while absorbing less than a `rho` fraction of that slice's core. Congestion is needed only if an external bridge specifically requires distinct unweighted witnesses; an internally distinct single core already gives congestion one nonuniformly.

## Formal status

`verification/pnp-linear-random-list/PNPSharpBuriedSliceFinite.lean` formalizes the rational sharp-mass inequality, the constant seven, monotonicity in absorption, and the conditional-average scalar step. It does not formalize finite-list double counting, circuits, probability, NP uniformity, magnification, or P versus NP. No fresh Lean kernel replay was available in this runtime.
