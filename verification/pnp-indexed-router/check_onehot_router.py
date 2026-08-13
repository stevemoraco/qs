def bits(k, a):
    r = k.bit_length() - 1
    out = []
    for p in range(r - 1, -1, -1):
        w = 1 << p
        hit = False
        s = w
        while s < k:
            if s <= a < s + w:
                hit = True
                break
            s += 2 * w
        out.append(int(hit))
    return out

checked = 0
for r in range(1, 13):
    k = 1 << r
    count = (k - 1) + sum((1 << q) - 1 for q in range(r))
    assert count == 2 * k - 2 - r
    for a in range(k):
        want = [int(c) for c in f"{a:0{r}b}"]
        assert bits(k, a) == want
        checked += 1
print("checked", checked, "one-hot inputs")
