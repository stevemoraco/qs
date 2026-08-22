#!/usr/bin/env python3
"""Exact finite regression certificates for the NS selective Leray atom.

This checker uses only Python's standard library and exact integers/Fractions.
It certifies finite algebra and enumerations only.  It does not certify an
analytic limit, an invariant manifold, a Navier--Stokes solution, or a Clay
Millennium conclusion.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys

Vec = tuple[Q, Q, Q]
assertion_count = 0


def vec(x: int | Q, y: int | Q, z: int | Q) -> Vec:
    return (Q(x), Q(y), Q(z))


def add(a: Vec, b: Vec) -> Vec:
    return tuple(x + y for x, y in zip(a, b))  # type: ignore[return-value]


def sub(a: Vec, b: Vec) -> Vec:
    return tuple(x - y for x, y in zip(a, b))  # type: ignore[return-value]


def scale(c: int | Q, a: Vec) -> Vec:
    c = Q(c)
    return tuple(c * x for x in a)  # type: ignore[return-value]


def dot(a: Vec, b: Vec) -> Q:
    return sum((x * y for x, y in zip(a, b)), Q(0))


def cross(a: Vec, b: Vec) -> Vec:
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def norm2(a: Vec) -> Q:
    return dot(a, a)


def sym_symbol(k: Vec, a: Vec, b: Vec) -> Vec:
    return add(scale(dot(a, k), b), scale(dot(b, k), a))


def leray_numerator(k: Vec, s: Vec) -> Vec:
    """|k|^2 P_k s, avoiding all division."""
    return sub(scale(norm2(k), s), scale(dot(s, k), k))


def leray(k: Vec, s: Vec) -> Vec:
    d = norm2(k)
    if d == 0:
        raise ZeroDivisionError("Leray projection requires a nonzero carrier")
    return scale(Q(1, 1) / d, leray_numerator(k, s))


def require(condition: bool, label: str) -> None:
    global assertion_count
    assertion_count += 1
    if not condition:
        raise AssertionError(label)


def require_eq(actual: object, expected: object, label: str) -> None:
    require(actual == expected, f"{label}: {actual!r} != {expected!r}")


# A. Parameterized selective atom.
atom_cases = 0
for A in (-3, -2, -1, 1, 2, 3):
    for H in (-3, -2, -1, 1, 2, 3):
        p = vec(A, 0, H)
        q = vec(-A, 0, H)
        u = vec(H, H, -A)
        v = vec(H, H, A)
        high_k = add(p, q)
        low_k = sub(p, q)
        high_s = sym_symbol(high_k, u, v)
        low_s = sym_symbol(low_k, u, v)

        require_eq(dot(p, u), Q(0), "p transverse")
        require_eq(dot(q, v), Q(0), "q transverse")
        require_eq(high_s, scale(-2 * A * A, high_k), "high longitudinal")
        require_eq(leray_numerator(high_k, high_s), vec(0, 0, 0),
                   "high Leray numerator")
        require_eq(low_s, vec(4 * A * H * H, 4 * A * H * H, 0),
                   "low raw symbol")
        require_eq(leray(low_k, low_s), vec(0, 4 * A * H * H, 0),
                   "low projected symbol")
        den = 2 * H * H + A * A
        require_eq(Q(2 * A * H * H, den),
                   Q(A) - Q(A * A * A, den),
                   "normalized coefficient")
        atom_cases += 1

# B. Third finite difference annihilates the packet quadratic.
moment_cases = 0
for H in range(-5, 6):
    for D in range(-4, 5):
        value = (
            (2 * H + 1) ** 2
            - 3 * (2 * H + 2 * D + 1) ** 2
            + 3 * (2 * H + 4 * D + 1) ** 2
            - (2 * H + 6 * D + 1) ** 2
        )
        require_eq(value, 0, "quadratic moment code")
        moment_cases += 1

# C. Minimal 2D3C atom and cross-frame pollution.
p = vec(1, 1, 0)
q = vec(-1, 1, 0)
u = vec(-1, 1, 1)
v = vec(-1, -1, 1)
require_eq(dot(p, u), Q(0), "minimal p transverse")
require_eq(dot(q, v), Q(0), "minimal q transverse")
minimal_high = sym_symbol(add(p, q), u, v)
minimal_low = sym_symbol(sub(p, q), u, v)
require_eq(minimal_high, vec(0, -4, 0), "minimal high raw")
require_eq(cross(add(p, q), minimal_high), vec(0, 0, 0),
           "minimal high longitudinal")
require_eq(minimal_low, vec(4, 0, -4), "minimal low raw")
require_eq(leray_numerator(sub(p, q), minimal_low), vec(0, 0, -16),
           "minimal low division-free certificate")
require_eq(leray(sub(p, q), minimal_low), vec(0, 0, -4),
           "minimal low projected")

p1, u1 = vec(1, 0, -1), vec(-1, 1, -1)
p2, u2 = vec(1, 1, 0), vec(-1, 1, 1)
cross_k = add(p1, p2)
cross_s = sym_symbol(cross_k, u1, u2)
require_eq(cross_s, vec(2, -2, 2), "two-frame raw pollution")
require_eq(leray(cross_k, cross_s), vec(2, -2, 2),
           "two-frame projected pollution")
require(cross(cross_k, cross_s) != vec(0, 0, 0),
        "two-frame pollution is transverse")

# D. General fixed-frame 2D3C symbol: the retained output is purely normal.
passive_cases = 0
for a in (-3, -2, -1, 1, 2, 3):
    for H in (-3, -2, -1, 1, 2, 3):
        for c in (-2, -1, 1, 2):
            p = vec(a, H, 0)
            q = vec(-a, H, 0)
            u = vec(-H, a, c * H)
            v = vec(-H, -a, c * H)
            high_k = add(p, q)
            low_k = sub(p, q)
            high_s = sym_symbol(high_k, u, v)
            low_s = sym_symbol(low_k, u, v)
            require_eq(high_s, scale(-2 * a * a, high_k),
                       "2D3C high longitudinal")
            require_eq(leray_numerator(high_k, high_s), vec(0, 0, 0),
                       "2D3C high killed")
            require_eq(low_s, vec(4 * a * H * H, 0, -4 * c * a * H * H),
                       "2D3C low raw")
            require_eq(leray(low_k, low_s), vec(0, 0, -4 * c * a * H * H),
                       "2D3C low is purely passive")
            passive_cases += 1

# E. Isosceles relay: exact desired fibers plus omitted same-carrier polarization.
iso_p, iso_q, iso_k = vec(1, 0, 0), vec(0, 1, 0), vec(-1, -1, 0)
iso_a, iso_b, iso_n = vec(0, 1, -1), vec(-1, 0, 1), vec(0, 0, 1)
iso_r = vec(0, 1, 1)
require_eq(add(add(iso_p, iso_q), iso_k), vec(0, 0, 0),
           "isosceles carrier relation")
require_eq(dot(iso_p, iso_a), Q(0), "isosceles p transverse")
require_eq(dot(iso_q, iso_b), Q(0), "isosceles q transverse")
require_eq(dot(iso_k, iso_n), Q(0), "isosceles k transverse")
require_eq(leray(add(iso_p, iso_q),
                 sym_symbol(add(iso_p, iso_q), iso_a, iso_b)),
           vec(0, 0, 2), "isosceles active sum")
require_eq(leray(sub(iso_p, iso_q),
                 sym_symbol(sub(iso_p, iso_q), iso_a, iso_b)),
           vec(0, 0, 0), "isosceles conjugate difference killed")
reciprocal = leray(add(iso_q, iso_k),
                   sym_symbol(add(iso_q, iso_k), iso_b, iso_n))
require_eq(reciprocal, iso_n, "isosceles full reciprocal output")
require_eq(iso_n, add(scale(Q(-1, 2), iso_a), scale(Q(1, 2), iso_r)),
           "isosceles reciprocal polarization decomposition")
require_eq(dot(iso_a, iso_r), Q(0), "isosceles omitted polarization orthogonal")
require_eq(dot(add(iso_q, iso_k), iso_r), Q(0),
           "isosceles omitted polarization transverse")
require(cross(iso_n, iso_a) != vec(0, 0, 0),
        "isosceles reciprocal not in selected polarization")

# F. Minimal noncoplanar three-plane braid and unique exterior fiber.
e1, e2, e3 = vec(1, 0, 0), vec(0, 1, 0), vec(0, 0, 1)
k12, k13, k23 = vec(-1, -1, 0), vec(-1, 0, -1), vec(0, -1, 1)
a12, b12, n12 = vec(0, 1, -1), vec(-1, 0, 1), e3
a13, b13, n13 = vec(0, -1, -1), vec(1, 1, 0), e2
require_eq(dot(e1, a13), Q(0), "braid second shared carrier transverse")
require_eq(dot(e3, b13), Q(0), "braid second pump transverse")
require_eq(dot(k13, n13), Q(0), "braid second target transverse")
require(cross(a12, a13) != vec(0, 0, 0),
        "braid shared polarizations span the transverse plane")
require_eq(leray(sub(e2, e3), sym_symbol(sub(e2, e3), b12, b13)),
           vec(-2, 0, 0), "braid cross-plane active relay")
require_eq(leray(add(e2, e3), sym_symbol(add(e2, e3), b12, b13)),
           vec(0, 0, 0), "braid cross-plane conjugate killed")
ext_k = vec(1, 2, 0)
require_eq(leray(ext_k, sym_symbol(ext_k, b12, n12)),
           vec(0, 0, -1), "braid exterior pollution")
braid_positive = [e1, e2, e3, scale(-1, k12), scale(-1, k13), scale(-1, k23)]
braid_modes = set(braid_positive + [scale(-1, x) for x in braid_positive])
require_eq(len(braid_modes), 12, "braid real support size")
decompositions = []
braid_ordered = sorted(braid_modes)
for i, x in enumerate(braid_ordered):
    for y in braid_ordered[i:]:
        if add(x, y) == ext_k:
            decompositions.append((x, y))
require_eq(len(decompositions), 1, "braid exterior unordered fiber unique")
require_eq(set(decompositions[0]), {e2, scale(-1, k12)},
           "braid exterior unique decomposition")

# G. Scalable shear cancellation: many potential labels, zero Euler symbol.
shear_modes = [vec(n, 0, 0) for n in range(-4, 5) if n]
for x in shear_modes:
    for y in shear_modes:
        require_eq(sym_symbol(add(x, y), vec(0, 1, 0), vec(0, 1, 0)),
                   vec(0, 0, 0), "shear symbol cancellation")
differences = {sub(x, y) for x in shear_modes for y in shear_modes}
require(len(differences) > len(shear_modes), "shear has a large difference set")

# H. Exact finite multiplicity firewalls.
circle = [(x, y) for x in range(-5, 6) for y in range(-5, 6)
          if x * x + y * y == 25]
require_eq(len(circle), 12, "radius-five oriented circle")
lines = {min((x, y), (-x, -y)) for x, y in circle}
require_eq(len(lines), 6, "radius-five unoriented lines")

modes: set[Vec] = set()
for a in (1, 2):
    for h in (1, 2):
        for sx in (-1, 1):
            for st in (-1, 1):
                modes.add(vec(sx * a, st * h, 0))
                modes.add(vec(sx * a, 0, st * h))
require_eq(len(modes), 32, "off-shell universe size")
ordered = sorted(modes)
sum_counts: Counter[Vec] = Counter()
for i, x in enumerate(ordered):
    for y in ordered[i:]:
        sum_counts[add(x, y)] += 1
require_eq(sum(sum_counts.values()), 528, "unordered pair count")
require_eq(len(sum_counts), 297, "sum-label count")
require_eq(dict(sorted(Counter(sum_counts.values()).items())),
           {1: 160, 2: 104, 4: 28, 8: 4, 16: 1},
           "sum multiplicity histogram")
require_eq(sum_counts[vec(2, 1, 1)], 1, "positive singleton fiber")
require_eq(sum_counts[vec(2, -1, -1)], 1, "negative singleton fiber")
require_eq(sum_counts[vec(0, 1, 1)], 4, "zero-axial repair multiplicity")

# I. Sharp finite leakage inequality, checked on an exact witness family.
amplitudes = {i: vec(i - 3, 2 - i, i % 2) for i in range(7)}
target = {0, 3}
threshold = Q(2)
good = {i for i, z in amplitudes.items() if norm2(z) >= threshold * threshold}
outside_energy = sum((norm2(z) for i, z in amplitudes.items() if i not in target), Q(0))
rhs = threshold * threshold * max(len(good) - len(target), 0)
require(outside_energy >= rhs, "sharp conditional leakage inequality")

# J. Exact rational exterior/Picard parameter ledgers (finite algebra only).
nu, d2, a2, coupling, N = Q(3, 2), Q(4), Q(5), Q(7), 4
mu = nu * (d2 + a2 * Q(2 * N - 1, 2) ** 2) - 2 * coupling
require(mu > 0, "Jacobi exterior coercive parameter gate")

beta, core_norm, epsilon = Q(1, 8), Q(1), Q(5, 8)
delta = 1 - 2 * beta * core_norm
discriminant = delta * delta - 4 * beta * epsilon
sqrt_discriminant = Q(1, 2)
radius = Q(1)
contraction = Q(1, 2)
require_eq(discriminant, sqrt_discriminant * sqrt_discriminant,
           "Picard exact square discriminant")
require_eq(beta * radius * radius - delta * radius + epsilon, Q(0),
           "Picard radius quadratic")
require_eq(contraction, 1 - sqrt_discriminant, "Picard contraction ledger")
require(0 < contraction < 1, "Picard strict contraction ledger")

source_bytes = Path(__file__).read_bytes()
report = {
    "assertions": assertion_count,
    "atom_cases": atom_cases,
    "moment_cases": moment_cases,
    "passive_2d3c_cases": passive_cases,
    "circle_points": len(circle),
    "off_shell_modes": len(modes),
    "off_shell_pair_labels": len(sum_counts),
    "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
    "status": "finite exact algebra verified; no analytic or Clay conclusion",
}
require(assertion_count >= 1000, "expected broad exact regression coverage")
report["assertions"] = assertion_count
print(json.dumps(report, sort_keys=True, separators=(",", ":")))
