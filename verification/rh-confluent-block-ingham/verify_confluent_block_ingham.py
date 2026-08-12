#!/usr/bin/env python3
"""Finite numerical falsifier for the explicit confluent block Ingham floor."""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class Case:
    ratio: float
    max_order: int
    carriers: int
    geometry: str
    trial: int


def carrier_frequencies(rng, carriers, h, geometry):
    if carriers <= 1:
        return np.array([0.0])
    if geometry == "arithmetic":
        gaps = np.full(carriers - 1, h)
    elif geometry == "alternating":
        gaps = np.array([h if j % 2 == 0 else h * (2.5 + 0.25 * (j % 5)) for j in range(carriers - 1)])
    elif geometry == "bounded_random":
        gaps = h * (1.0 + 3.0 * rng.random(carriers - 1))
    elif geometry == "exponential_gaps":
        gaps = h * (1.0 + rng.exponential(scale=1.0, size=carriers - 1))
    else:
        raise ValueError(geometry)
    tau = np.concatenate(([0.0], np.cumsum(gaps)))
    tau -= float(np.mean(tau))
    return tau


def minimum_spacing(tau):
    return math.inf if len(tau) <= 1 else float(np.min(np.diff(np.sort(tau))))


def orders_for(rng, carriers, max_order, geometry):
    if geometry == "arithmetic":
        return np.full(carriers, max_order, dtype=int)
    if geometry == "alternating":
        return np.array([1 + (j % max_order) for j in range(carriers)], dtype=int)
    return rng.integers(1, max_order + 1, size=carriers, endpoint=False)


def gram_matrix(a, tau, orders):
    labels = [(p, r) for p, order in enumerate(orders) for r in range(int(order))]
    gram = np.zeros((len(labels), len(labels)), dtype=np.complex128)
    for row, (p, r) in enumerate(labels):
        for col, (q, s) in enumerate(labels):
            z = (2.0 * a) / (2.0 * a + 1j * (tau[q] - tau[p]))
            gram[row, col] = math.comb(r + s, r) * z ** (r + s + 1)
    return (gram + gram.conj().T) / 2.0


def block_floor(ratio, max_order):
    shape = max_order**2 + max_order * math.sqrt(max_order**2 - 1.0)
    return 3.0 / (2.0 * (4.0**max_order - 1.0)) * math.exp(-8.0 * math.pi * ratio * shape)


def parse_csv(text, cast):
    return [cast(item.strip()) for item in text.split(",") if item.strip()]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--ratios", default="0.005,0.01,0.02,0.05,0.1")
    parser.add_argument("--orders", default="1,2,3,4")
    parser.add_argument("--carriers", default="2,5,12")
    parser.add_argument("--trials", type=int, default=12)
    parser.add_argument("--seed", type=int, default=260812)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    args = parser.parse_args()

    ratios = parse_csv(args.ratios, float)
    max_orders = parse_csv(args.orders, int)
    carrier_counts = parse_csv(args.carriers, int)
    geometries = ["arithmetic", "alternating", "bounded_random", "exponential_gaps"]
    rng = np.random.default_rng(args.seed)
    records = []

    for ratio in ratios:
        for max_order in max_orders:
            for carriers in carrier_counts:
                for geometry in geometries:
                    count = 1 if geometry in {"arithmetic", "alternating"} else args.trials
                    for trial in range(count):
                        tau = carrier_frequencies(rng, carriers, 1.0, geometry)
                        spacing = minimum_spacing(tau)
                        orders = orders_for(rng, carriers, max_order, geometry)
                        gram = gram_matrix(ratio * spacing, tau, orders)
                        eigenvalues = np.linalg.eigvalsh(gram)
                        floor = block_floor(ratio, max_order)
                        records.append({
                            "ratio": ratio,
                            "max_order": max_order,
                            "carrier_count": carriers,
                            "dimension": int(np.sum(orders)),
                            "geometry": geometry,
                            "trial": trial,
                            "actual_spacing": spacing,
                            "proved_floor": floor,
                            "observed_minimum": float(eigenvalues[0]),
                            "observed_maximum": float(eigenvalues[-1]),
                            "verified": bool(eigenvalues[0] + args.tolerance >= floor),
                        })

    local = []
    for order in max_orders:
        matrix = np.array([[math.comb(r + s, r) for s in range(order)] for r in range(order)], dtype=float)
        values = np.linalg.eigvalsh(matrix)
        floor = 3.0 / (4.0**order - 1.0)
        local.append({
            "order": order,
            "proved_floor": floor,
            "observed_minimum": float(values[0]),
            "observed_maximum": float(values[-1]),
            "verified": bool(values[0] + args.tolerance >= floor),
        })

    all_checks = all(row["verified"] for row in records) and all(row["verified"] for row in local)
    certificate = {
        "honesty": "FINITE NUMERICAL FALSIFICATION ONLY; NOT THE INFINITE THEOREM; NOT RH",
        "seed": args.seed,
        "case_count": len(records),
        "all_checks_pass": all_checks,
        "local_pascal_checks": local,
        "sample_records": records[:12],
    }
    rendered = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    print(rendered, end="")
    print("sha256=" + hashlib.sha256(rendered.encode()).hexdigest())
    return 0 if all_checks else 1


if __name__ == "__main__":
    raise SystemExit(main())
