# Yang--Mills — modified Fredholm determinant has no Hilbert--Schmidt norm-only positive lower bound, even on invertible rank-one operators

Date: 2026-08-13 UTC

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 📚 SOURCE-VERIFIED against Jiazheng Liu, Preprints.org `202604.0332`, latest displayed version v2, posted 9 April 2026; 🟢 PROVED exact rank-one and invertible near-resonance counterexamples; 🔴 REFUTED the manuscript's universal Carleman determinant lower bound and every repair depending only on a bounded Hilbert--Schmidt norm; 🧱 quantitative spectral distance, actual Hilbert--Schmidt tail convergence, and the determinant-to-physical-spectrum theorem remain load-bearing; 🔵 LEAN-SOURCE finite core staged separately; ✅ LEAN-VERIFIED pending replay. **NOT YANG--MILLS. FIVE-ALARM OFF.**

## 1. The claimed universal bound

The manuscript defines the modified Fredholm determinant of a Hilbert--Schmidt operator `A` by

`det_2(I-A)=prod_j (1-lambda_j) exp(lambda_j)`

and claims a universal positive lower bound of the form

`|det_2(I-A)| >= exp(-c ||A||_HS^2)>0.`

The same manuscript records the correct zero criterion: `det_2(I-A)=0` when `1` is an eigenvalue of `A`.

## 2. Exact one-dimensional contradiction

Take the one-dimensional Hilbert space `C` and

`A=[1].`

Then `A` is rank one and Hilbert--Schmidt, with

`||A||_HS^2=1.`

Its modified determinant is exactly

`det_2(I-A)=(1-1) exp(1)=0.`

The claimed lower bound would give

`0 >= exp(-c)>0`,

an immediate contradiction for every finite real `c`.

## 3. Invertible near-resonance strengthening

Excluding the exact eigenvalue `1` does not rescue any norm-only uniform lower bound.

For `0<epsilon<1`, take

`A_epsilon=[1-epsilon].`

Then `I-A_epsilon=[epsilon]` is invertible and

`||A_epsilon||_HS=1-epsilon<1.`

But

`boxed:
det_2(I-A_epsilon)
 = epsilon exp(1-epsilon).`

Therefore

`det_2(I-A_epsilon)->0`

as `epsilon->0+`, while all operators remain invertible and their Hilbert--Schmidt norms remain bounded by one.

More explicitly, for any proposed constant `c>0`, choose

`0<epsilon<exp(-c-1).`

Since `exp(1-epsilon)<e`,

`epsilon exp(1-epsilon)<epsilon e<exp(-c).`

Also `||A_epsilon||_HS^2<1`, so

`exp(-c ||A_epsilon||_HS^2)>exp(-c).`

Hence

`|det_2(I-A_epsilon)|
 < exp(-c)
 < exp(-c ||A_epsilon||_HS^2),`

contradicting the claimed bound even inside the invertible rank-one class.

Thus:

`boxed:
Hilbert--Schmidt norm control does not quantify distance from the resonance 1 in the spectrum.}`

The needed quantity is an inverse/resolvent or spectral-distance bound, not merely an ideal norm.

## 4. The cutoff estimate does not construct the continuum determinant

The manuscript's displayed cutoff estimate is of the form

`||K_0 V_L||_HS^2 <= C sum_(ell<=L) 1/ell ~ C log L.`

This upper bound diverges with the cutoff. It proves neither

`K_0V in I_2`

nor

`||K_0(V-V_L)||_HS->0.`

The elementary sequence

`S_L=sum_(ell=1)^L 1/ell`

is the canonical countertype: every partial sum is finite, but the sequence is not bounded and its tail does not converge in the claimed square-summable norm.

A continuum determinant requires a Cauchy theorem in the `I_2` norm. Finite cutoff determinants alone do not supply it.

## 5. Even determinant nonvanishing is not yet the Clay mass gap

Suppose, after repair, one proves

`det_2(I-gK_0V(0)) != 0`

and analyticity in a neighborhood of the momentum parameter. That yields a local zero-free neighborhood for this determinant.

To become the official Yang--Mills mass gap, three further theorems are required:

1. the continuum, nontrivial, gauge-invariant quantum Yang--Mills theory exists and satisfies the required axioms;
2. zeros of this determinant coincide exactly with the non-vacuum physical Hamiltonian spectrum on the reconstructed Hilbert space;
3. the determinant normalization and zero-free radius are regulator independent in physical units.

A perturbative or cutoff operator determinant is not automatically the Osterwalder--Schrader/Wightman physical transfer spectrum.

## 6. Claim + counterexamples + salvage

### Claim killed

For every Hilbert--Schmidt `A`, the modified determinant is bounded away from zero by a universal positive function of `||A||_HS`.

### Counterexamples

- Exact: `A=[1]`, giving determinant zero.
- Invertible near-resonance: `A_epsilon=[1-epsilon]`, giving determinant `epsilon exp(1-epsilon)->0` with norm at most one.

### Best salvage

A viable determinant route must prove, for the actual gauge-invariant continuum operator,

`dist(1,Spec(A(0))) >= eta>0`

or equivalently an appropriate uniform inverse/resolvent estimate; prove convergence in the relevant Schatten norm; and prove that the determinant zeros are exactly the physical non-vacuum mass spectrum after OS/Wightman reconstruction.

## 7. Assumptions and critic verdict

### Assumptions

- Standard definition of the modified determinant for Hilbert--Schmidt operators.
- In one dimension, the sole eigenvalue supplies the sole determinant factor.
- The manuscript's inequality and cutoff bounds are read literally.
- No hidden Yang--Mills-specific spectral exclusion is imported into a theorem stated for all Hilbert--Schmidt operators.

### Critic verdict

🟢 **SURVIVES.** The exact counterexample is dimension one and finite rank; no convergence or physics subtlety enters it. The near-resonance family blocks the natural repair “assume invertible.”

🔴 **REFUTED AS WRITTEN:** the v2 Carleman determinant theorem establishes nonvanishing or a mass gap.

🟡 **CONDITIONAL:** a problem-specific coercivity theorem and a full constructive QFT bridge could revive a determinant route.

## 8. Lean status

- 🔵 LEAN-SOURCE: `verification/b2-round42/YMCarlemanDeterminantFirewall.lean` formalizes the scalar determinant factor at eigenvalue one, its positivity contradiction, and the elementary near-resonance product estimate under an abstract exponential upper bound.
- ✅ LEAN-VERIFIED: pending clean replay.
- Hilbert spaces, Schatten ideals, Fredholm determinants, spectra, analytic operator families, gauge theory, OS/Wightman reconstruction, and Yang--Mills are not formalized.

## 9. Exact remaining gap

🚧 MISSING — a regulator-uniform physical-sector inverse theorem, Schatten-tail convergence, nontrivial continuum reconstruction, and an exact determinant-to-Hamiltonian-spectrum identification with a positive physical zero-free radius.

## 10. Provenance

- Exact round parent: `stevemoraco/qs@e345ef906a7b809e3c47e949e556b6417247ed06`.
- Source audit predecessor: `stevemoraco/RH@d6d4112f8d31e616e4bb10d6b2cbc18221e6bec7`.
- Current primary record checked 2026-08-13: Jiazheng Liu, *Pure Analytic Calculations of the Mass Gap and Glueball Spectrum in Four-Dimensional Yang-Mills Theory*, Preprints.org manuscript `202604.0332`, latest displayed version v2.
- Official problem scope: Clay Mathematics Institute, *Yang--Mills and Mass Gap*.

**FIVE-ALARM OFF.**
