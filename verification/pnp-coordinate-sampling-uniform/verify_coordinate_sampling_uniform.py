#!/usr/bin/env python3
"""Exact finite falsifier for coordinate-sampling compression.

This script uses small sparse sets consisting of constants, literals, and
negated literals. It enumerates every NO string, computes the exact one-sketch
false-accept probability by inclusion-exclusion over the sparse YES set, and
checks a seeded simultaneous list of N fingerprints.

It is finite evidence only. It does not formalize MCSP, P-uniformity, P, NP, or
an asymptotic magnification theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
from fractions import Fraction
from pathlib import Path


def literal_truth_tables(ell: int) -> list[int]:
    length = 1 << ell
    all_ones = (1 << length) - 1
    tables = {0, all_ones}
    for variable in range(ell):
        table = 0
        for index in range(length):
            value = (index >> (ell - 1 - variable)) & 1
            if value:
                table |= 1 << index
        tables.add(table)
        tables.add(all_ones ^ table)
    return sorted(tables)


def hamming_distance(left: int, right: int) -> int:
    return (left ^ right).bit_count()


def fingerprint(table: int, sample: tuple[int, ...]) -> tuple[int, ...]:
    return tuple((table >> coordinate) & 1 for coordinate in sample)


def accepts_sample(table: int, yes_tables: list[int], sample: tuple[int, ...]) -> bool:
    target = fingerprint(table, sample)
    return any(fingerprint(candidate, sample) == target for candidate in yes_tables)


def exact_single_sample_probability(
    table: int,
    yes_tables: list[int],
    length: int,
    sample_count: int,
) -> Fraction:
    """Inclusion-exclusion for the union of fingerprint-collision events."""
    probability = Fraction(0, 1)
    table_count = len(yes_tables)
    for mask in range(1, 1 << table_count):
        selected = [
            yes_tables[index]
            for index in range(table_count)
            if (mask >> index) & 1
        ]
        common_coordinates = 0
        for coordinate in range(length):
            bit = (table >> coordinate) & 1
            if all(((candidate >> coordinate) & 1) == bit for candidate in selected):
                common_coordinates += 1
        term = Fraction(common_coordinates, length) ** sample_count
        if mask.bit_count() % 2:
            probability += term
        else:
            probability -= term
    return probability


def find_good_list(
    no_tables: list[int],
    yes_tables: list[int],
    length: int,
    sample_count: int,
    repetitions: int,
    seed: int,
    trial_budget: int,
) -> tuple[int, list[tuple[int, ...]]]:
    rng = random.Random(seed)
    best_bad_count = len(no_tables)
    for trial in range(trial_budget):
        sample_list = [
            tuple(rng.randrange(length) for _ in range(sample_count))
            for _ in range(repetitions)
        ]
        bad_count = sum(
            all(accepts_sample(table, yes_tables, sample) for sample in sample_list)
            for table in no_tables
        )
        best_bad_count = min(best_bad_count, bad_count)
        if bad_count == 0:
            return trial, sample_list
    raise RuntimeError(
        f"no simultaneous list found; best remaining NO count={best_bad_count}"
    )


def run_case(ell: int, eta: Fraction, seed: int, trial_budget: int) -> dict[str, object]:
    length = 1 << ell
    yes_tables = literal_truth_tables(ell)
    distance = math.ceil(float(eta * length))
    no_tables = [
        table
        for table in range(1 << length)
        if min(hamming_distance(table, candidate) for candidate in yes_tables)
        >= distance
    ]

    sample_count = math.ceil(
        math.log(4 * len(yes_tables)) / float(eta)
    )
    exact_probabilities = [
        exact_single_sample_probability(
            table, yes_tables, length, sample_count
        )
        for table in no_tables
    ]
    maximum_probability = max(exact_probabilities, default=Fraction(0, 1))

    union_bound = Fraction(len(yes_tables), 1) * (
        Fraction(length - distance, length) ** sample_count
    )

    good_trial, good_list = find_good_list(
        no_tables=no_tables,
        yes_tables=yes_tables,
        length=length,
        sample_count=sample_count,
        repetitions=length,
        seed=seed,
        trial_budget=trial_budget,
    )

    yes_perfect = all(
        all(accepts_sample(table, yes_tables, sample) for sample in good_list)
        for table in yes_tables
    )
    no_rejected = all(
        any(not accepts_sample(table, yes_tables, sample) for sample in good_list)
        for table in no_tables
    )

    return {
        "ell": ell,
        "truth_table_length": length,
        "yes_table_count": len(yes_tables),
        "no_table_count": len(no_tables),
        "distance_threshold": distance,
        "eta_numerator": eta.numerator,
        "eta_denominator": eta.denominator,
        "coordinates_per_fingerprint": sample_count,
        "simultaneous_repetitions": length,
        "maximum_exact_single_false_accept_numerator": maximum_probability.numerator,
        "maximum_exact_single_false_accept_denominator": maximum_probability.denominator,
        "maximum_exact_single_false_accept": float(maximum_probability),
        "crude_union_bound": float(union_bound),
        "single_error_below_quarter": maximum_probability <= Fraction(1, 4),
        "seeded_good_list_trial": good_trial,
        "yes_perfect_completeness": yes_perfect,
        "all_no_inputs_rejected": no_rejected,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=260812)
    parser.add_argument("--trial-budget", type=int, default=5000)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()

    cases = [
        run_case(2, Fraction(1, 4), arguments.seed + 2, arguments.trial_budget),
        run_case(3, Fraction(1, 4), arguments.seed + 3, arguments.trial_budget),
    ]
    certificate: dict[str, object] = {
        "status": "exact finite falsification evidence only; not P versus NP",
        "seed": arguments.seed,
        "cases": cases,
        "all_cases_verified": all(
            case["single_error_below_quarter"]
            and case["yes_perfect_completeness"]
            and case["all_no_inputs_rejected"]
            for case in cases
        ),
    }
    encoded_without_digest = json.dumps(certificate, indent=2, sort_keys=True)
    certificate["certificate_sha256_without_digest_field"] = hashlib.sha256(
        encoded_without_digest.encode("utf-8")
    ).hexdigest()
    encoded = json.dumps(certificate, indent=2, sort_keys=True) + "\n"

    if arguments.output is None:
        print(encoded, end="")
    else:
        arguments.output.write_text(encoded, encoding="utf-8")

    if not certificate["all_cases_verified"]:
        raise SystemExit("a finite coordinate-sampling check failed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
