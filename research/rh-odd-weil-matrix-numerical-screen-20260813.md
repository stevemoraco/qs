# RH localized odd-Weil matrix numerical screen

Date: 2026-08-13 UTC

Status: **double-precision normalization/falsification screen; not interval
arithmetic; not a theorem; no RH conclusion; SIX-ALARM OFF.**

## Purpose

The script

```text
verification/rh/odd_weil_matrix_screen.py
```

assembles the actual localized odd sine matrix from Suzuki's explicit screw
function.  It is intended to catch a sign or normalization error cheaply and
to measure how quickly finite Schur margins can collapse.  It is not used as
evidence of positivity.

For `x>=0`, it evaluates

```text
Psi(x)=4(e^(x/2)+e^(-x/2)-2)
       -sum_{n<=e^x} Lambda(n)/sqrt(n)(x-log n)
       +(x/2)(psi(1/4)-log pi)
       +(C-e^(-x/2)Phi(e^(-2x),2,1/4))/4.
```

The Lerch endpoint is evaluated by the exact root-of-unity identity

```text
e^(-x/2) Phi(e^(-2x),2,1/4)
 = 4[Li_2(w)-i Li_2(iw)-Li_2(-w)+i Li_2(-iw)],
w=e^(-x/2).
```

It then uses the exact elementary overlap integral to reduce

```text
H_jk=-(pi^2 j k/a^3)
  integral integral Psi(t-u)cos(pi j u/a)cos(pi k t/a) du dt
```

to one dimension.  Gauss--Legendre panels are split at every prime-power
kink `log n`.  Two quadrature orders are run independently, and the script
reports symmetry, matrix eigenvalues, finite high-block eigenvalues, Schur
eigenvalues, and the Loewner decrement at each added high mode.

## Reproduction

Environment:

```text
Python 3.12.13
NumPy 2.3.5
SciPy 1.17.0
```

Command:

```text
python3 verification/rh/odd_weil_matrix_screen.py \
  --a 0.6931471805599453 --dimension 16 --low 2 --order 768
```

Source identity:

```text
Git blob  478bb6945a2d394f3fce32158c6eebf286fc6add
SHA-256   145507c2a09c8277bd0a4c8b5d6cdfb54939cf288bd30d4dbc7df91d3e0bc44e
```

Selected output:

```text
STATUS=HEURISTIC_DOUBLE_PRECISION_NOT_A_CERTIFICATE
a=0.69314718055994529
dimension=16
orders=384,768
max_order_difference=2.7213079789589756e-08
max_symmetry_defect=0
lerch_at_zero=17.197329154507116
psi_at_zero=0
matrix_min_eigenvalue=6.3475947050458121e-10
matrix_max_eigenvalue=3.0492218480533131

schur cutoff=3
  min=3.3537199959161792e-06
  max=9.8577702056609571e-03
  finite_high_min=1.3172496980517094

schur cutoff=8
  min=1.3130276787870298e-09
  max=5.9145111236280621e-05
  finite_high_min=1.3497171071858338e-01
  step_loewner_min=-7.81e-19
  step_loewner_max=2.3234406940512464e-05

schur cutoff=16
  min=6.3524352946810609e-10
  max=3.9000646845284095e-05
  finite_high_min=1.0698455609868042e-01
  step_loewner_min=-1.33e-18
  step_loewner_max=4.1629062931651653e-08
```

Every reported Schur step was positive semidefinite up to absolute rounding
noise below `5e-18`, as the exact block algebra predicts.  Raising the order
from `192/384` to `384/768` reduced the maximum entry change from
`4.33e-7` to `2.72e-8`.

## Claimant, critic, rebuilder

**Claimant.**  The finite screen passes four independent normalization tests:
`Psi(0)=0`, the Lerch constant equals `17.1973291545...`, matrix symmetry is
exact in the assembly, and successive Schur complements have the correct
Loewner direction.  At this cutoff, the finite high block remains comfortably
positive while the smallest low Schur margin falls by more than three orders
of magnitude between cutoffs `3` and `8`.

**Critic.**  None of the displayed signs is certified.  The smallest matrix
and Schur eigenvalues are below the observed entrywise order difference, so
they cannot even be assigned a rigorous sign from this run.  Gauss--Legendre
order comparison is not an error bound, IEEE evaluation of the dilogarithm is
not outward rounded, and a finite high eigenvalue does not bound the infinite
high block.  The collapse of the Schur margin is therefore a warning, not RH
evidence.

**Rebuilder.**  Reproduce the same panel decomposition with ball arithmetic,
prove an analytic remainder bound on every panel (including the origin and
prime kinks), and combine it with an effective infinite high-sector floor and
the fixed-parameter all-row theorem.  Until those steps are closed, use this
program only to falsify formulas and choose test parameters.

## Exact lesson

The screen demonstrates why a positive finite high block and a positive
finite Schur complement cannot be promoted silently.  Even in a numerically
stable assembly, the apparent Schur margin can become much smaller than the
entry error while the high block still looks well conditioned.  The missing
residual/cofinal theorem is quantitatively load-bearing.

**SIX-ALARM: OFF.  NUMERICAL SCREEN BANKED.**
