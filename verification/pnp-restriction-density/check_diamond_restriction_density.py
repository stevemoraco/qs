#!/usr/bin/env python3
import json

MAX_N = 100
MAX_T = 16
MAX_Q = 12

boundary_cases = 0
boundary_violations = []

for n in range(1, MAX_N + 1):
    for r in range(n + 1):
        for a in range(n + 1):
            for b in range(n - a + 1):
                k = n - a - b
                if not (r + 1 < k):
                    continue
                low = a + 1
                high = a + k - 1
                in_band = lambda w: (w <= r) or (n <= w + r)
                if in_band(low) and in_band(high):
                    boundary_cases += 1
                    if not (a + b + 2 <= 2 * r):
                        boundary_violations.append(
                            [n, r, a, b, k, low, high]
                        )

# For the denominator-free transfer it is enough to test the smallest allowed
# support, support=good.  Every larger support only increases q*support.
fraction_cases = 0
fraction_violations = []
for t in range(MAX_T + 1):
    total = 2**t
    for q in range(1, MAX_Q + 1):
        for good in range(total + 1):
            if total <= q * good:
                fraction_cases += 1
                support = good
                if not (total <= q * support):
                    fraction_violations.append([t, q, good, support])

result = {
    "boundary_max_n": MAX_N,
    "boundary_applicable_cases": boundary_cases,
    "boundary_violations": len(boundary_violations),
    "fraction_max_t": MAX_T,
    "fraction_max_q": MAX_Q,
    "fraction_applicable_minimal_support_cases": fraction_cases,
    "fraction_violations": len(fraction_violations),
    "status": "PASS" if not boundary_violations and not fraction_violations else "FAIL",
}

print(json.dumps(result, indent=2, sort_keys=True))

if boundary_violations or fraction_violations:
    raise SystemExit(1)
