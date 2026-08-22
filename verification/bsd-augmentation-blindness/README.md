# Public verifier — BSD augmentation-localization blindness finite core

**Status:** finite abstract algebra only. **Not** a formalization of Iwasawa theory, elliptic curves, Tamagawa numbers, or BSD.

## Canonical private provenance

- Repository: `stevemoraco/RH-Lean`
- Branch: `agent/bsd-augmentation-localization-p-blindness-20260812`
- Private note: `research/bsd/BSD_AUGMENTATION_LOCALIZATION_P_BLINDNESS_2026-08-12.md`
- Exact Lean blob mirrored here: `6eb3913dc24e954cdafd4e9f4e62a0b6fccd5bc4`

## Replayed declarations

1. `power_multiple_associated_after_map`
2. `original_associated_power_multiple_after_map`
3. `positive_integral_shift_changes_order`
4. `integral_shift_eq_iff`
5. `separate_bounds_give_max`
6. `max_strictly_below_sum`
7. `two_local_factors_do_not_add_in_one_chain`

## Mathematical scope

The core proves only:

- if the image of a distinguished element is a unit, multiplying by any power of it does not change the associated class after mapping;
- an integral order still changes by a positive exponent;
- one scalar divisibility chain retains the maximum of local exponents, not their additive sum.

It does not formalize:

- `O[[T]]`;
- localization at the augmentation height-one prime;
- determinant or fundamental lines;
- Kato's zeta element;
- Kurihara numbers;
- dual exponentials or period comparison;
- elliptic curves, Selmer groups, component groups, or BSD.

A green replay validates only these seven declarations and their printed axiom reports.

Five-alarm status: OFF.
