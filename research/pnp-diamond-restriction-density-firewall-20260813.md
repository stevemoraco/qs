# P versus NP braid: sparse restriction-density and diamond codimension firewalls

Date: 2026-08-13
Branch: `agent/gpt56-pnp-diamond-restriction-firewall-20260813-run4`
Status: finite counting/geometry obstruction and strategy correction; **not** P versus NP.

## Executive result

Two tempting ways to combine the newly Lean-verified restriction-averaging transfer with the low-surplus `B_2` critical-path obstruction are now sharply delimited.

First, there is a completely general sparsity barrier for **oblivious uniform restriction assignments**. Fix any set of `t` coordinates. For a positive support `P subset {0,1}^n`, each positive string induces exactly one assignment on those coordinates. Therefore the number of assignments whose codimension-`t` subcube contains even one positive point is at most `|P|`. Among all `2^t` assignments,

\[
\boxed{
\Pr[\text{the restricted language is nonempty}]\le |P|/2^t.
}
\]

Consequently, if a constant `1/q` fraction of the assignments is to expose any nontrivial local hard gadget, necessarily

\[
\boxed{2^t\le q|P|.}
\]

For the Chen--Li--Yang sparsity ceiling `|P| <= n^{alpha(n)}` with `alpha(n) <= log n/log log n`, constant-mass oblivious restrictions can therefore fix only

\[
t\le \log_2 |P|+O(1)=O((\log^2 n)/(\log\log n))
\]

coordinates. In particular, a uniform-assignment restriction distribution of depth `Theta(n/log log n)` has vanishing positive mass and cannot directly feed a constant-`rho` local-to-global averaging theorem.

Second, the current explicit symmetric language

\[
L_n^\diamond=\{x:|x|\in\{1,2,n-1\}\}
\]

has a stronger **two-sided geometry** obstruction. More generally suppose every accepted Hamming layer lies in a boundary band of radius `r`:

\[
w\le r\quad\text{or}\quad n-r\le w.
\]

Fix `a` coordinates to one and `b` coordinates to zero, leaving `k=n-a-b` live variables. If the restricted language still contains both a low local positive of free weight `1` and a high local positive of free weight `k-1`, and `k>r+1`, then

\[
\boxed{a+b+2\le 2r.}
\]

Thus a boundary-supported symmetric sparse language cannot preserve the low/high diamond marker geometry under a deep restriction. This remains true even if the restriction distribution is conditioned on hitting the positive support.

These results do **not** refute restriction averaging in general. The exact survivor is important: the averaging theorem accepts an arbitrary nonnegative restriction distribution. We may condition on a circuit-independent family of positive-bearing restrictions, and no efficient sampler is required merely to contradict a pointwise-error guarantee. What is killed is the hope that a deep, oblivious, uniform assignment restriction will simultaneously (i) retain constant local hard mass and (ii) remove enough of a `2n+O(n/log log n)` circuit to cross the strict local `2k-2` boundary. For symmetric boundary-shell gadgets, even support conditioning cannot retain the two-sided marker pattern at large codimension.

The next construction therefore has to be genuinely non-symmetric: a sparse language with many deliberately chosen deep subcubes carrying local hard gadgets, while avoiding the visible-anchor shortcut that lets a circuit test the frozen prefix too cheaply.

## 1. General fixed-coordinate restriction-density theorem

Let `P` be any finite subset of `{0,1}^n`. Fix a coordinate set `F` of size `t`. For each assignment `a in {0,1}^F`, let `Q_a` be the subcube obtained by fixing `F=a`.

Define

\[
G_F=\{a:Q_a\cap P\ne\varnothing\}.
\]

Projection onto `F` gives a surjection from `P` onto `G_F`, hence

\[
|G_F|\le |P|.
\]

Since there are exactly `2^t` assignments,

\[
\frac{|G_F|}{2^t}\le\frac{|P|}{2^t}.
\]

This theorem has no circuit hypothesis, no symmetry hypothesis, and no complexity-class hypothesis. Averaging over an arbitrary distribution on the *choice of coordinate set* `F` preserves the same upper bound so long as the assignment on the chosen coordinates is uniform.

A useful denominator-free form is: if at least a `1/q` fraction of assignments is good, then

\[
2^t\le q|G_F|\le q|P|.
\]

This is exactly the finite form formalized in the accompanying Lean core.

### Relation to the older branching firewall

The banked branch `agent/pnp-sparse-restriction-public-verifier-20260811` proves that if a support realizes **all** Boolean patterns on `t` selected coordinates then its size is at least `2^t`. The new observation is the quantitative density version needed for restriction averaging: even obtaining a constant fraction of nonempty patterns already forces support exponential in `t`, up to the constant denominator.

## 2. Why this matters at the magnification sparsity ceiling

If

\[
|P_n|\le n^{\alpha(n)},
\qquad
\alpha(n)\le\frac{\log n}{\log\log n},
\]

then

\[
\log_2|P_n|\le \alpha(n)\log_2 n
=O\!\left(\frac{\log^2n}{\log\log n}\right).
\]

Therefore any fixed-coordinate restriction experiment that uses uniformly random assignments and asks for constant mass of *nonempty* restrictions is limited to polylogarithmic codimension. Requiring a richer local pattern only decreases the good mass.

This is a proof-strategy firewall, not a circuit lower bound. A small number of fixed variables can in principle collapse many gates, so one may not silently infer that polylogarithmic codimension is incapable of removing `Theta(n/log log n)` gates. The correct conclusion is narrower: a proposed shrinkage theorem cannot obtain its constant good mass merely from deep uniform assignments while also requiring a positive local gadget.

## 3. Two-sided boundary-shell codimension theorem

Define the boundary band

\[
B_{n,r}=\{w: w\le r\ \text{or}\ n\le w+r\}.
\]

The second disjunct is the subtraction-free form of `n-r <= w`.

Fix `a` ones and `b` zeros and leave `k` variables free, so

\[
a+b+k=n.
\]

A free point of local weight `1` has ambient weight

\[
w_{\rm lo}=a+1.
\]

A free point of local weight `k-1` has ambient weight

\[
w_{\rm hi}=a+k-1=n-b-1.
\]

Assume `k>r+1` and both ambient weights lie in `B_{n,r}`.

The low point cannot lie in the upper band: `n <= a+1+r` together with `n=a+b+k` would imply `k<=r+1`. Hence

\[
a+1\le r.
\]

Likewise the high point cannot lie in the lower band: `a+k-1<=r` contradicts `k>r+1`. Therefore it lies in the upper band,

\[
n\le (n-b-1)+r,
\]

so

\[
b+1\le r.
\]

Adding gives

\[
\boxed{a+b+2\le2r.}
\]

The theorem only needs the free-weight `1` and `k-1` positives. The free-weight `2` layer used by `L_n^diamond` is unnecessary for this codimension obstruction.

For `L_n^diamond` itself, `r=2` already suffices for the positive layers at weights `1,2,n-1`; hence any restriction retaining both the local weight-1 and local weight-`k-1` positives with `k>3` fixes at most two variables. The all-zero/all-one two-face marker argument therefore cannot be recursively replayed after a deep restriction of this same symmetric language.

## 4. Symmetric sparsity makes the boundary radius small

For a symmetric language, accepting one Hamming weight `w` means accepting the entire shell of size `binom(n,w)`. Thus a size upper bound on the language forces accepted weights toward the two boundaries.

A convenient elementary quantitative checkpoint is this. Suppose `|P_n| <= n^A`, `A>=1`, and `n>4A^2`. The standard bound

\[
\binom nk\ge(n/k)^k
\]

at `k=2A` gives

\[
\binom n{2A}>n^A.
\]

By binomial unimodality, no accepted symmetric layer can have distance at least `2A` from both boundaries. Therefore all accepted weights lie in a boundary band of radius at most `2A-1`, and the two-sided theorem implies that a diamond-preserving restriction fixes only `O(A)` variables.

At the CLY ceiling, one can take `A=O(log n/log log n)` after the usual integer rounding, so this symmetric two-sided route is limited to `O(log n/log log n)` fixed variables, even under support conditioning.

The asymptotic shell estimate is recorded here as a human corollary; the accompanying Lean file deliberately formalizes only the load-bearing finite boundary-band implication, avoiding a hidden import of binomial asymptotics.

## 5. Conditioning is a survivor, not a class-preservation failure

A tempting overstatement would be: “sparse languages cannot use deep restriction averaging because almost every deep restriction is empty.” That is false as a general proof-method claim.

The verified finite averaging theorem on branch `b2/pnp-restriction-replay-20260813` permits an arbitrary normalized nonnegative restriction weight `mu`. To refute a probabilistic circuit with a pointwise error guarantee, the induced global input distribution need not be efficiently samplable: any normalized distribution witnessing average error at least `delta` contradicts the assertion that every point has error `<delta`.

Therefore one may condition `mu` on a fixed family of positive-bearing restrictions. What must remain circuit-independent (if it is to directly supply a common minimax core) is the restriction/input weighting used against the deterministic circuits; efficient NP sampling is not itself required by this finite minimax step.

The real cost of conditioning is structural: the selected restrictions have to make **every** low-surplus circuit locally vulnerable with enough common mass. For the symmetric diamond language the codimension theorem blocks the obvious two-sided local gadget. For a non-symmetric construction, the open task is to arrange many deep hard slices without exposing a cheap visible selector/anchor circuit.

## 6. Claimant / critic / rebuilder

### Claimant

Use the Lean-verified local-to-global restriction averaging lemma. Choose deep restrictions that simplify `2n+S` circuits below a local strict threshold, prove a constant fraction of them expose a local diamond hard core, and average the local error back to a pointwise lower bound.

### Critic

Under oblivious uniform assignments, a sparse positive support gives good mass at most `|P|/2^t`. At `t=Theta(n/log log n)` this is far below constant throughout the CLY sparsity range. For symmetric boundary-shell languages, conditioning does not repair the geometry: retaining both low and high local marker positives forces codimension `O(r)`, and sparsity itself keeps `r` polylogarithmic.

The density argument alone also does **not** imply a gate-shrinkage lower bound. A few fixed variables might trigger a large cascade in a particular circuit. Nor does conditioning automatically give a common hard distribution across circuits.

### Rebuilder

The highest-EV restriction target is now:

\[
\boxed{
\begin{gathered}
\text{an explicit non-symmetric sparse }P_n\in NP,\\
\text{a circuit-independent conditioned family of deep restrictions},\\
\text{constant local-hard mass for every }2n+O(n/\log\log n)\ B_2\text{ circuit},\\
\text{and no visible-anchor shortcut that refunds the baseline.}
\end{gathered}}
\]

Equivalently, build a sparse family of overlapping deep hard slices whose selector complexity is itself paid by the same exact slack ledger. This is a more precise target than “randomly restrict until the circuit is small.”

## 7. Barrier/model audit

- **Class preservation:** the density and boundary-band theorems are finite set/arithmetic statements. They do not promote a nonuniform set to NP. Conditioning a proof distribution does not itself assert an efficient NP sampler.
- **Circuit model:** no gate lower bound is imported here. The intended downstream application remains unrestricted fan-in-two `B_2`; the firewall is model-independent.
- **Relativization:** both finite theorems relativize. They do not evade relativization and must not be advertised as doing so.
- **Natural proofs:** no large constructive truth-table property is produced.
- **Algebrization:** no arithmetization occurs.
- **Finite-to-asymptotic:** the exact finite inequalities are the banked result. The asymptotic CLY comparison uses only the stated sparsity ceiling and elementary logarithms; it is not a P-vs-NP conclusion.

## 8. Provenance and relation to existing bank

This note builds on, without overwriting:

1. `verification/pnp-restriction-averaging/PNPRestrictionAveraging.lean` on branch `b2/pnp-restriction-replay-20260813`, whose finite Fubini/local-to-global transfer was freshly replayed in GitHub Actions after its nonnegativity hypotheses were corrected.
2. `verification/pnp-sparse-restriction/PNPSparseRestrictionBranchingFinite.lean` on branch `agent/pnp-sparse-restriction-public-verifier-20260811`, which already formalizes the all-patterns `2^t` support barrier.
3. `verification/pnp-symmetric-restriction-density/PNPSymmetricRestrictionDensity.lean` on branch `agent/pnp-symmetric-restriction-density-public-verifier-20260812`, which formalizes a complementary two-color central-layer density core.
4. `research/pnp-orientation-marker-firewall-20260813.md` on the parent branch, source of the explicit `L_n^diamond` low/high marker geometry.

The new contribution is the constant-fraction restriction image bound, the exact two-sided boundary-shell codimension inequality, and the correction that arbitrary support conditioning survives the first density barrier but not the symmetric two-sided geometry barrier.

FIVE-ALARM: OFF.
