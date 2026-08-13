# Six-color Navier--Stokes packet: exact quartic return obstruction

**Date:** 2026-08-13  
**Status:** exact finite Fourier/Leray obstruction to extending the verified
one-step radial-isolation claim to quartic closure; **not a Navier--Stokes
solution or blowup theorem**.

## 1. Audited construction

This audit uses exactly the six-color carriers and polarizations compiled in
`stevemoraco/qs` PR #207, head
`991d27587d3d85209fd56e82888e08ec6a257676`.

For nonzero output frequency (K), write

[
P_K(w)=w-K(K\cdot w)/|K|^2
]

and suppress the common Fourier Navier--Stokes factor (-i). The symmetrized
unordered-pair interaction is

[
B(k,u;l,v)=P_{k+l}((u\cdot l)v+(v\cdot k)u).
]

## 2. Small exact rectangle

Use

[
q_2=(1,-1,0),quad \ell_2=(-7,-7,10),quad h_2=(-20,-20,-28),
]

[
a=\ell_2+h_2=(-27,-27,-18),quad
b=\ell_2-h_2=(13,13,38),quad
c=(10,29,29).
]

With the exact transverse polarizations

[
u_a=(7129,7127,-21384),quad
u_b=(-15049,-15047,10296),quad
u_c=(-22968,3959,3961),
]

one has (a\cdot u_a=b\cdot u_b=c\cdot u_c=0). The first-generation
sidebands are

[
s=a+c=(-17,2,11),quad |s|^2=414,
]

[
r=b-c=(3,-16,9),quad |r|^2=346,
]

and

[
s+r=(-14,-14,20)=2\ell_2.
]

Exact rational projection gives

[
B(a,u_a;c,u_c)=-48599324(29,-67,57),
]

[
B(b,u_b;-c,u_c)=-(1117784452/173)(725,-3,-247).
]

Their second interaction returns exactly to the color-2 target line:

[
B(s,B_s;r,B_r)
=-\frac{6176372472021338295808}{173}(1,-1,0)\ne0.
]

For a real field, the amplitude phase is
(A_aA_bA_cA_{-c}=A_aA_b|A_c|^2), so this is a coherent rectangle.

The heat detuning is only

[
\Delta=|s+r|^2-|s|^2-|r|^2=792-414-346=32.
]

Thus the intermediate pair jointly decays at rate (760), slower than the
target rate (792); the Duhamel denominator is only (32) before common
spatial rescaling. Exhaustive exact enumeration of the 144 simple rectangles
(six target colors times 24 signed choices of (c)) leaves 114 with nonzero
two-stage coefficient, and this example (with one coordinate mate) minimizes
(|\Delta|) among them.

## 3. Uniqueness and structural firewalls

Among all (24\cdot25/2=300) unordered high-carrier pairs with replacement,
(s) has exactly one decomposition and (r) has exactly one decomposition.
Thus neither first-stage sideband can be canceled by another high-pair path.

The support obstruction is universal. Every desired pair (a,b) and every
other real conjugate pair (c,-c) satisfy

[
(a+c)+(b-c)=a+b.
]

Hence no real carrier family containing two conjugate pairs can achieve
frequency-only isolation beyond quadratic depth. In the equal-shell geometry
(a=\ell+h), (b=\ell-h), (lambda=2\ell), and
(|c|^2=|\ell|^2+|h|^2), direct expansion gives

[
\Delta=|\lambda|^2-|a+c|^2-|b-c|^2=-4h\cdot(h+c).
]

Here (|h|^2=1584) and (h\cdot c=-1592), so (Delta=32).

## 4. Claimant, critic, rebuilder

**Claimant.** PR #207 correctly verifies common shells, transversality,
same-color desired output, vanishing self-harmonics, and a cross-color radial
gap at the first high--high interaction level.

**Critic.** Pairwise radial separation is not nonlinear closure. The explicit
unique sidebands above interact one generation later and return with a nonzero,
minimally heat-detuned coefficient at the designated low frequency. Summing
all ordered binary interaction trees for the square-free monomial
(A_aA_bA_cA_{-c}) also leaves a nonzero transverse coefficient, so the
displayed path is not canceled automatically by other quartic
parenthesizations. Linear viscosity cannot modify this leading
amplitude-degree-four, time-cubic coefficient, though it changes later time
orders.

**Rebuilder.** The new first missing arrow is an exact quartic normal-form
theorem. A viable construction must cancel the full quartic return polynomial
through a proved amplitude/phase relation while preserving the desired
quadratic channels, or prove the returned channel quantitatively absorbable at
every scale. A specially tied full-packet schedule could still lie in the
return polynomial's zero locus; that is the next finite falsification target.

## 5. Exact replay

`tools/check_ns_six_color_quartic_return.py` uses exact integers and
`fractions.Fraction`. The denominator-free Lean file proves the carrier
geometry, transversality, heat detuning, both first Leray numerators, the
nonzero return into (q_2), and the universal conjugate-pair rectangle.

**SIX-ALARM: OFF.**
