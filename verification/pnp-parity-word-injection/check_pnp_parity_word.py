#!/usr/bin/env python3
"""Exact finite hostile checker for the parity-word random-walk core.

This checker is discovery/falsification evidence, not a proof for all q and k.
All arithmetic is integral and every enumerated word is checked exactly.
"""

from collections import Counter
from itertools import permutations, product
import hashlib
import inspect
import json


def odd_support(word):
    parity = set()
    for letter in word:
        if letter in parity:
            parity.remove(letter)
        else:
            parity.add(letter)
    return frozenset(parity)


def first_swap(word, u, v):
    out = list(word)
    for i, letter in enumerate(out):
        if letter == u:
            out[i] = v
            break
        if letter == v:
            out[i] = u
            break
    return tuple(out)


assertions = 0
word_cases = 0
tagged_cases = 0
recurrences = []
radial_bounds = []
monotone_steps = []

left = first_swap((2, 1, 0), 1, 2)
right = first_swap((3, 1, 0), 1, 3)
assert left == (1, 1, 0)
assert right == (1, 1, 0)
assert (2, 1, 0) != (3, 1, 0)
assertions += 3

counts = {}
for q in range(1, 7):
    alphabet = tuple(range(q))
    for k in range(0, 9):
        radial = Counter()
        endpoints = Counter()
        for word in product(alphabet, repeat=k):
            endpoint = odd_support(word)
            radial[len(endpoint)] += 1
            endpoints[endpoint] += 1
            word_cases += 1
            for u in alphabet:
                for v in alphabet:
                    image = first_swap(word, u, v)
                    assert len(image) == len(word)
                    assert first_swap(image, u, v) == word
                    assertions += 2
            for u, v in permutations(endpoint, 2):
                image = first_swap(word, u, v)
                assert odd_support(image) == endpoint.symmetric_difference({u, v})
                assert u not in odd_support(image)
                assert v not in odd_support(image)
                tagged = (image, u, v)
                recovered = (first_swap(tagged[0], tagged[1], tagged[2]), u, v)
                assert recovered == (word, u, v)
                assertions += 4
                tagged_cases += 1
        assert sum(radial.values()) == q ** k
        assert sum(endpoints.values()) == q ** k
        assertions += 2
        counts[(q, k)] = radial

for q in range(1, 7):
    for k in range(0, 7):
        m1 = counts[(q, k)][1]
        m3 = counts[(q, k)][3]
        m1_next = counts[(q, k + 2)][1]
        recurrence_rhs = (3 * q - 2) * m1 + 6 * m3
        assert m1_next == recurrence_rhs
        assertions += 1
        recurrences.append((q, k))
        radial_rhs = (q - 1) * (q - 2) * m1
        assert 6 * m3 <= radial_rhs
        assertions += 1
        radial_bounds.append((q, k))
        assert m1_next * (q ** k) <= m1 * (q ** (k + 2))
        assertions += 1
        monotone_steps.append((q, k))
    assert counts[(q, 3)][1] == q * (3 * q - 2)
    assertions += 1

source = inspect.getsource(odd_support) + inspect.getsource(first_swap)
print(json.dumps({
    "status": "finite exact parity-word audit passed",
    "scope": {"q": [1, 6], "k": [0, 8], "universal_claim": False},
    "assertions": assertions,
    "word_cases": word_cases,
    "tagged_cases": tagged_cases,
    "recurrence_cases": len(recurrences),
    "radial_cases": len(radial_bounds),
    "monotone_cases": len(monotone_steps),
    "tagless_collision": {
        "source_left": [2, 1, 0], "tag_left": [1, 2],
        "source_right": [3, 1, 0], "tag_right": [1, 3],
        "common_image": [1, 1, 0],
    },
    "q_edge_cases": {
        "q1_p3_numerator": counts[(1, 3)][1],
        "q2_p3_numerator": counts[(2, 3)][1],
        "q1_p3_denominator": 1,
        "q2_p3_denominator": 8,
    },
    "kernel_sha256": hashlib.sha256(source.encode()).hexdigest(),
    "boundary": (
        "Exact exhaustive computation only; the Lean universal involution "
        "theorems are separate, and the aggregate recurrence remains a "
        "universal theorem obligation."
    ),
}, indent=2, sort_keys=True))
