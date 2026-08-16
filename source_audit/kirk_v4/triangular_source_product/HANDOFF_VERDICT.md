# Kirk v4 Theorem 5.26 -> Lemma 8.1 source-norm handoff verdict

Status: source/dependency closure, not independent verification of the analytic theorems and not a Yang--Mills or Clay proof.

## Question

Does the manuscript merely assert at Lemma 8.1 that triangular source-renormalization products are bounded, or is the needed product theorem already supplied in the same source space/norm before matching?

## Exact source chain

1. **One finite source space.** Lemma 5.21 defines the finite graded curvature-jet quotient `J_{<=D}` and permits adjoining the retained/source/displacement/stress/rotation and one/two-root marks used later.

2. **Exact normalized one-step transport.** Proposition 5.24 defines

   `T_D(u,rho) : J_{<=D} -> J_{<=D}`

   as the exact normalized marked one-step source transport in the finite jet matrix norm.

3. **Product theorem.** Lemma 5.25 controls the principal fundamental matrix by a fixed running-log power and gives strict complementary contraction. Theorem 5.26 then chooses normalized source coordinates, sums the triangular inhomogeneous forcing, supplies the physical-scale suppression for higher-dimensional defects, and gives uniform finite Schwartz-seminorm bounds for every fixed marked row. It explicitly ends at the compact first-crossing handoff.

4. **Same permanent marked norm reaches matching.** Theorem 5.27 supplies one uniformly equivalent one-step norm `||.||_*`, on a domain independent of volume, microscopic cutoff, and preceding weak depth. Its item U5 controls zero-, one-, and two-root connector rows and every prescribed finite passive-source order in that same domain. Section 6 states that its purpose is to print the exact norm bound consumed by the compact-group macrobridge.

5. **Matching roots use that norm.** Theorem 6.44 forms each complete source contact cluster before matching and measures the resulting local roots in the **permanent finite source-renormalization norm**. Its constant may depend on the fixed source orders and root types but not on volume, cutoff, exterior configuration, or preceding weak depth.

6. **Section 8 applies the same declared normalization.** Lemma 8.1 first performs geometric averaging, whose `l_infinity` and Riemann-weighted `l_1` inequalities are proved explicitly, and then applies the finite triangular source-renormalization matrix. Its phrase “after the declared source normalization” refers to the preceding normalized `J_{<=D}` transport, not to a new untyped matrix family. Theorem 8.9 later explicitly cites the finite triangular source theorem in Part V for the local Schwartz/source seminorm, and Theorem 8.11 uses those same triangular source-renormalization seminorms for the local vertices.

7. **Later reuse confirms the type.** Section 8.2 again calls `J_{<=D}` the finite-dimensional renormalized curvature-jet source multiplet, and Lemma 8.44 states that finite triangular source renormalization conjugates its finite-dimensional action.

## Repaired proof of the Lemma 8.1 source sentence

For one fixed finite jet family, write `P_{j<-m}` for the product of the exact normalized source transports furnished by Lemma 5.25/Theorem 5.26 in the permanent norm of Theorem 5.27. The source theorem gives

`||P_{j<-m} v||_root <= C_D ||v||_root`

with `C_D` independent of cutoff, volume, exterior data and weak depth after the declared physical/logarithmic source normalization.

Let `A_{j<-m}` be the geometric block averaging in Lemma 8.1. Its displayed inequalities give contraction in both the componentwise sup norm and the Riemann-weighted `l_1` source mass. Hence

`||P_{j<-m} A_{j<-m} v||_root <= C_D ||v||_root`.

This changes only the fixed local-root constant. It cannot change the spatial connector exponent because the source matrix acts inside the already contracted endpoint root, exactly as Theorem 6.44 states.

## Verdict

The initial generic objection remains mathematically valid: bounded individual triangular factors do not imply bounded products. But it does not refute this source chain because Lemma 5.25/Theorem 5.26 are a genuine product/normalization theorem and Theorem 5.27 carries the same fixed marked source family to matching.

Therefore retire

`YM-KIRK-526-TO-81-NORMALIZED-ROOT-NORM-IDENTITY`

at **source/dependency level**, conditional on the truth of Theorems 5.25--5.27 themselves.

The next live Yang--Mills obligations are the substantive analytic estimates and continuum handoff, not another abstract norm-identity lemma. In particular, source/dependency closure does not kernel-verify:

- the infinite-dimensional weak RG theorem;
- the compact/mixed forest estimates;
- the common continuum Schwinger family;
- Osterwalder--Schrader reconstruction;
- a positive physical mass gap;
- nontriviality or dimensional-transmutation identification; or
- the Jaffe--Witten/Clay theorem.

FIVE-ALARM OFF.
