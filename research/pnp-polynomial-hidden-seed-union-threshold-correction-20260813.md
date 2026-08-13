# Correction: polynomial hidden-seed union threshold

The first version of `pnp-polynomial-hidden-seed-union-20260813.md` described the `n=2^35` numerical value `0.897216796875` as an exact check of the full displayed probability bound. That wording omitted the positive term `n exp(-9nL)` from the numerical evaluation.

The theorem remains valid. For `n=2^L`, `L>=1`, use `exp(-9nL) < 2^(-9nL) < 1/n^3`, so `n exp(-9nL) < 1/n^2`. It is therefore enough to check

`1/n^2 + 25,165,824 L^2/n + 393,216 L/n^2 < 1`.

At `L=35`, `n=2^35`, the left side is exactly

`1059246632357554421761 / 1180591620717411303424`

and is approximately `0.8972167968750117`, hence below one. Each summand decreases under `L -> L+1` for `L>=3`, since the denominators gain factors `4`, `2`, and `4`, respectively, while the polynomial numerators grow by smaller ratios. Thus the sufficient bound stays below one for every power of two `n>=2^35`.

This correction changes only the finite threshold justification, not the hidden-seed union theorem or its `tau_f <= 8` consequence.
