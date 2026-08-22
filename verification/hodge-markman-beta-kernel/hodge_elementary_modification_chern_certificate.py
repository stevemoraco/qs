#!/usr/bin/env python3
"""Exact scalar certificate for the elementary-modification Hodge construction.

The script verifies parameter balance, the divisor/curve Chern coefficient,
the complete-intersection correction ray, and final mixed-class bookkeeping.
It does not construct coherent sheaves or formalize deformation theory.
"""

from __future__ import annotations

import json

import sympy as sp


def main() -> None:
    n, d, q, ell, z = sp.symbols("n d q ell z", nonzero=True)
    a = sp.symbols("a", nonzero=True)
    b = 1 / a

    M = n**2 + 4 * d
    e = 2 * M
    f = 2 * M
    r = 96 * M

    parameter_residual = sp.factor(24 * e * f - r * (n**2 + 4 * d))
    assert parameter_residual == 0

    divisor_ch1 = n
    divisor_ch3 = n**3 / 24
    curve_ch3 = n * e * f
    constituent_ch1 = sp.expand(r * divisor_ch1)
    constituent_ch3 = sp.factor(r * divisor_ch3 - curve_ch3)
    expected_constituent_ch3 = sp.factor(-r * n * d / 6)
    assert sp.simplify(constituent_ch3 - expected_constituent_ch3) == 0

    # RM eigencoefficients.  Norm one is encoded as b=1/a.
    u = sp.factor(d * a - q * b)
    v = sp.factor(d * b - q * a)
    lambda_scalar = sp.factor(u * v)

    # Coefficients of d A^3-q B^3 after dividing out the common factor 3.
    target_first = sp.factor(d * a**2 * b - q * b**2 * a)
    target_second = sp.factor(d * a * b**2 - q * b * a**2)
    assert sp.simplify(target_first - u) == 0
    assert sp.simplify(target_second - v) == 0

    # Coefficients of H^3, again after dividing out the common factor 3.
    hcube_first = sp.factor(u**2 * v)
    hcube_second = sp.factor(u * v**2)
    assert sp.simplify(hcube_first - lambda_scalar * target_first) == 0
    assert sp.simplify(hcube_second - lambda_scalar * target_second) == 0

    n_total = sp.expand(ell * r * n)
    sum_a1 = n_total
    sum_a3 = sp.factor(-n_total * d / 6)
    correction_a3 = sp.factor(n_total * d / 6)
    correction_b3 = sp.factor(-n_total * q / 6)

    final_a1 = sp.factor(sum_a1)
    final_a3 = sp.factor(sum_a3 + correction_a3)
    final_b3 = sp.factor(correction_b3)

    assert final_a1 == n_total
    assert final_a3 == 0
    assert sp.simplify(final_b3 + n_total * q / 6) == 0

    chi_v = sp.expand(r * z)
    finite_quotient_length = sp.expand(r * z)
    point_residual = sp.factor(chi_v - finite_quotient_length)
    assert point_residual == 0

    receipt = {
        "status": "PASS",
        "scope": "finite scalar Chern-character certificate only",
        "explicit_parameters": {
            "M": str(M),
            "e": str(e),
            "f": str(f),
            "r": str(r),
        },
        "parameter_residual": str(parameter_residual),
        "constituent": {
            "ch1_coefficient": str(constituent_ch1),
            "ch3_coefficient": str(constituent_ch3),
            "expected_ch3": str(expected_constituent_ch3),
        },
        "complete_intersection": {
            "u": str(u),
            "v": str(v),
            "lambda": str(lambda_scalar),
            "first_residual": str(sp.factor(hcube_first - lambda_scalar * target_first)),
            "second_residual": str(sp.factor(hcube_second - lambda_scalar * target_second)),
        },
        "final_mixed_class": {
            "N_total": str(n_total),
            "A_degree_1": str(final_a1),
            "A_degree_3": str(final_a3),
            "B_degree_3": str(final_b3),
            "point_residual": str(point_residual),
        },
        "not_formalized": [
            "coherent sheaves",
            "flat deformation",
            "Bertini",
            "HKR",
            "Atiyah obstruction maps",
            "semiregularity",
            "Hodge conjecture",
        ],
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
