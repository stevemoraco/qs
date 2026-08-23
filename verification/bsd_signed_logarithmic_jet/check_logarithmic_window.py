def trim(a, p):
    while len(a) > 1 and a[-1] % p == 0:
        a.pop()
    return [x % p for x in a]


def add(a, b, p):
    n = max(len(a), len(b))
    c = [0] * n
    for i in range(n):
        c[i] = ((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % p
    return trim(c, p)


def mul(a, b, p):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] = (c[i + j] + x * y) % p
    return trim(c, p)


def pow_poly(a, n, p):
    out = [1]
    base = a[:]
    while n:
        if n & 1:
            out = mul(out, base, p)
        base = mul(base, base, p)
        n >>= 1
    return out


def cyclotomic_p_power_shifted(p, m):
    one_plus_x = [1, 1]
    out = [0]
    stride = p ** (m - 1)
    for t in range(p):
        out = add(out, pow_poly(one_plus_x, t * stride, p), p)
    return trim(out, p)


def phi_degree(p, m):
    return p ** (m - 1) * (p - 1)


def reach(p, N, parity):
    return sum(phi_degree(p, m) for m in range(1, N + 1) if m % 2 == parity)


def closed_reach(p, N, parity):
    a = N // 2
    if N % 2 == 0:
        if parity == 1:
            return (p ** (2 * a) - 1) // (p + 1)
        return p * (p ** (2 * a) - 1) // (p + 1)
    if parity == 1:
        return (p ** (2 * a + 2) - 1) // (p + 1)
    return p * (p ** (2 * a) - 1) // (p + 1)


checks = 0
for p in [3, 5, 7]:
    for m in range(1, 4):
        got = cyclotomic_p_power_shifted(p, m)
        d = phi_degree(p, m)
        expected = [0] * d + [1]
        assert got == expected, (p, m, len(got) - 1, d)
        checks += 1

for p in [3, 5, 7, 11, 13]:
    for N in range(1, 9):
        for parity in [0, 1]:
            assert reach(p, N, parity) == closed_reach(p, N, parity)
            checks += 1

for p in [3, 5, 7]:
    for N in range(1, 6):
        for parity in [0, 1]:
            R = reach(p, N, parity)
            finite = [(7 * i + 3) % p for i in range(R + 5)]
            H = [(5 * i + 1) % p for i in range(7)]
            correction = [0] * (R + 1) + H
            stable = finite[:]
            if len(stable) < len(correction):
                stable += [0] * (len(correction) - len(stable))
            for i, x in enumerate(correction):
                stable[i] = (stable[i] + x) % p
            assert stable[: R + 1] == finite[: R + 1]
            checks += R + 1

for p in [3, 5, 7, 11, 13]:
    assert reach(p, 1, 1) == p - 1
    assert reach(p, 2, 0) == p * (p - 1)
    checks += 2

print(
    "BSD_LOG_WINDOW_PASS",
    f"checks={checks}",
    "phi_pm_shifted_mod_p=X^phi",
    "jet_depth=O(log_p r)",
    "official_bsd=off",
)
