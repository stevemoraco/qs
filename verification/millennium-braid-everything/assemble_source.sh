#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

PARTS=(
  source-xz-b64/part-00.b64
  source-xz-b64/part-01.b64
  source-xz-b64/part-02.b64
  source-xz-b64/part-03.b64
  source-xz-b64/part-04.b64
  source-xz-b64/part-05-06.b64
  source-xz-b64/part-07-08.b64
  source-xz-b64/part-09-10.b64
  source-xz-b64/part-11-12.b64
  source-xz-b64/part-13.b64
)

for part in "${PARTS[@]}"; do test -s "$part"; done

(
  cd source-xz-b64
  sha256sum --check --strict SHA256SUMS
)

python3 - <<'PY'
from pathlib import Path
from difflib import SequenceMatcher
import base64, hashlib

paths = [
    'source-xz-b64/part-00.b64', 'source-xz-b64/part-01.b64',
    'source-xz-b64/part-02.b64', 'source-xz-b64/part-03.b64',
    'source-xz-b64/part-04.b64', 'source-xz-b64/part-05-06.b64',
    'source-xz-b64/part-07-08.b64', 'source-xz-b64/part-09-10.b64',
    'source-xz-b64/part-11-12.b64', 'source-xz-b64/part-13.b64',
]
parts = [''.join(c for c in Path(p).read_text() if not c.isspace()) for p in paths]
print('lengths=' + repr([len(p) for p in parts]))
corrupt = parts[2]
extra = corrupt[8000:]
print(f'extra_len={len(extra)} extra_sha256={hashlib.sha256(extra.encode()).hexdigest()}')

for i, text in enumerate(parts):
    if i == 2:
        continue
    pos = text.find(extra)
    print(f'exact_extra_in_part_{i}={pos}')

for i in [0, 1, 3, 4, 5, 6, 7, 8, 9]:
    m = SequenceMatcher(None, corrupt, parts[i], autojunk=False).find_longest_match()
    print(f'longest_match_part02_part{i}: a={m.a} b={m.b} size={m.size}')

neighbors = parts[1] + parts[3]
m = SequenceMatcher(None, corrupt, neighbors, autojunk=False).find_longest_match()
print(f'longest_match_part02_neighbors: a={m.a} b={m.b} size={m.size}')

m = SequenceMatcher(None, extra, parts[3], autojunk=False).find_longest_match()
print(f'longest_match_extra_part03: extra={m.a} part03={m.b} size={m.size}')
m = SequenceMatcher(None, extra, parts[1], autojunk=False).find_longest_match()
print(f'longest_match_extra_part01: extra={m.a} part01={m.b} size={m.size}')

# Test every simple 8,000-character window of the 9,861-character shard.
prefix = ''.join(parts[:2])
suffix = ''.join(parts[3:])
target = '52ec1001a3ee33b33e0ad1c1a024d572396850dd3c6a926299da45a6b2664578'
for start in range(0, 1862):
    candidate_part = corrupt[start:start + 8000]
    payload = base64.b64decode(prefix + candidate_part + suffix, validate=True)
    if hashlib.sha256(payload).hexdigest() == target:
        print(f'exact_window_recovery_start={start}')
        Path('MillenniumBraidEverything.lean.xz').write_bytes(payload)
        break
else:
    print('exact_window_recovery_start=NONE')

# Emit the prefix candidate for XZ integrity diagnostics.
payload = base64.b64decode(prefix + corrupt[:8000] + suffix, validate=True)
Path('MillenniumBraidEverything.lean.xz').write_bytes(payload)
print('prefix_candidate_sha256=' + hashlib.sha256(payload).hexdigest())
PY

# This diagnostic is intentionally expected to fail until exact source
# transport is recovered; preserve the candidate and all geometry in receipt.
xz --test MillenniumBraidEverything.lean.xz
