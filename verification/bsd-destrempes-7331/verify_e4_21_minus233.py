#!/usr/bin/env python3
"""Exact arithmetic certificate for the Destrempes--Malinin Theorem 5 audit.

This script uses only Python integer arithmetic.  It verifies the finite
computations for E_4(21,-233) and ell=7331.  It does not prove the published
deep theorem identifying the true order of Sha, the Galois-image theorem, or
any part of BSD.
"""

from __future__ import annotations

import json
from math import prod


def valuation(n: int, prime: int) -> int:
    n = abs(n)
    value = 0
    while n and n % prime == 0:
        n //= prime
        value += 1
    return value


def count_points_mod_prime(a2: int, a4: int, prime: int) -> int:
    """Count points on y^2=x^3+a2*x^2+a4*x over F_prime."""
    count = 1
    for x in range(prime):
        rhs = (x**3 + a2 * x**2 + a4 * x) % prime
        if rhs == 0:
            count += 1
        elif pow(rhs, (prime - 1) // 2, prime) == 1:
            count += 2
    return count


def main() -> None:
    n = 21
    parameter_p = -233
    ell = 7331
    t = 3 ** (2 * n + 1)
    a2 = 2 * (parameter_p - 8 * t)
    a4 = parameter_p**2
    discriminant = 16 * a4**2 * (a2**2 - 4 * a4)
    c4 = 16 * a2**2 - 48 * a4

    delta_factorization = {
        2: 10, 3: 43, 7: 3, 11: 1, 53: 1, 233: 4,
        446773: 1, 14696852993: 1,
    }
    assert abs(discriminant) == prod(
        p**e for p, e in delta_factorization.items()
    )

    conductor = 149845956054714394972728
    conductor_factorization = {
        2: 3, 3: 1, 7: 1, 11: 1, 53: 1, 233: 1,
        446773: 1, 14696852993: 1,
    }
    assert conductor == prod(p**e for p, e in conductor_factorization.items())
    assert conductor % ell != 0
    assert valuation(discriminant, 11) == 1
    assert c4 % 11 == 9

    A = 81 * a4 - 27 * a2**2
    B = 54 * a2**3 - 243 * a2 * a4
    delta_prime = 4 * A**3 + 27 * B**2
    short_discriminant = -16 * delta_prime
    assert short_discriminant == 3**12 * discriminant
    assert delta_prime % ell == 1475

    point_count = count_points_mod_prime(a2 % ell, a4 % ell, ell)
    frobenius_trace = ell + 1 - point_count
    assert point_count == 7376
    assert frobenius_trace == -44
    assert frobenius_trace % ell != 0

    sha_square_root = 410536
    assert sha_square_root == 2**3 * 7 * ell
    sha_order = sha_square_root**2
    assert valuation(sha_order, ell) == 2

    e1_a2 = 2 * parameter_p - 4 * t
    e1_a4 = parameter_p * (parameter_p - 4 * t)
    e1_delta = 16 * e1_a4**2 * (e1_a2**2 - 4 * e1_a4)
    e1_c4 = 16 * e1_a2**2 - 48 * e1_a4
    assert valuation(e1_delta, 11) == 2
    assert e1_c4 % 11 == 9
    assert valuation(e1_delta, 11) % ell != 0

    print(json.dumps({
        "curve": "E_4(21,-233)",
        "ell": ell,
        "a2": a2,
        "a4": a4,
        "conductor": conductor,
        "conductor_factorization": conductor_factorization,
        "discriminant_factorization": delta_factorization,
        "v_11_discriminant": valuation(discriminant, 11),
        "c4_mod_11": c4 % 11,
        "short_A": A,
        "short_B": B,
        "delta_prime_mod_ell": delta_prime % ell,
        "points_mod_ell": point_count,
        "frobenius_trace": frobenius_trace,
        "sha_order": sha_order,
        "v_ell_sha_order": valuation(sha_order, ell),
        "e1_v_11_discriminant": valuation(e1_delta, 11),
        "verified": True,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
