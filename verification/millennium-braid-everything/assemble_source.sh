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

for part in "${PARTS[@]}"; do
  test -s "$part"
done

(
  cd source-xz-b64
  echo 'actual shard hashes:'
  sha256sum part-*.b64
  echo 'actual shard byte counts:'
  wc -c part-*.b64
  echo 'pinned shard identity check:'
  sha256sum --check --strict SHA256SUMS
)

python3 - <<'PY'
from pathlib import Path
import base64
import hashlib

parts = [
    'source-xz-b64/part-00.b64',
    'source-xz-b64/part-01.b64',
    'source-xz-b64/part-02.b64',
    'source-xz-b64/part-03.b64',
    'source-xz-b64/part-04.b64',
    'source-xz-b64/part-05-06.b64',
    'source-xz-b64/part-07-08.b64',
    'source-xz-b64/part-09-10.b64',
    'source-xz-b64/part-11-12.b64',
    'source-xz-b64/part-13.b64',
]
alphabet = set('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=')
clean_parts = []
for part in parts:
    raw = Path(part).read_text()
    clean = ''.join(ch for ch in raw if not ch.isspace())
    bad = [(i, ch, ord(ch)) for i, ch in enumerate(clean) if ch not in alphabet]
    if bad:
        raise SystemExit(f'{part}: invalid base64 character(s): {bad[:20]}')
    print(f'{part}: raw={len(raw)} clean={len(clean)} mod4={len(clean)%4}')
    clean_parts.append(clean)

assert len(clean_parts[0]) == 8000
assert len(clean_parts[1]) == 8000
assert len(clean_parts[2]) == 9861
assert len(clean_parts[3]) == 8000
assert len(clean_parts[4]) == 8000
assert all(len(clean_parts[i]) == 16000 for i in range(5, 9))
assert len(clean_parts[9]) == 7164

# The exact compressed payload was independently pinned before transport.  The
# hosted replay proved that part-02 has 1,861 extra valid-base64 characters.
# Search every possible contiguous deletion of precisely that excess and accept
# a repair only when the decoded payload matches the original SHA-256.  This is
# a deterministic recovery certificate, not a heuristic truncation.
target_hash = '52ec1001a3ee33b33e0ad1c1a024d572396850dd3c6a926299da45a6b2664578'
expected_b64_len = 111164
excess = sum(map(len, clean_parts)) - expected_b64_len
assert excess == 1861
prefix = ''.join(clean_parts[:2])
corrupt = clean_parts[2]
suffix = ''.join(clean_parts[3:])
found = None
for cut in range(len(corrupt) - excess + 1):
    repaired_part = corrupt[:cut] + corrupt[cut + excess:]
    joined = prefix + repaired_part + suffix
    assert len(joined) == expected_b64_len
    try:
        payload = base64.b64decode(joined, validate=True)
    except Exception:
        continue
    digest = hashlib.sha256(payload).hexdigest()
    if digest == target_hash:
        found = (cut, corrupt[cut:cut + excess], payload)
        break
    if cut % 1000 == 0:
        print(f'hash_guided_recovery_progress={cut}')

if found is None:
    raise SystemExit('no contiguous 1,861-character deletion recovers pinned payload')
cut, dropped, payload = found
print(f'hash_guided_recovery_cut={cut}')
print(f'dropped_transport_duplicate_length={len(dropped)}')
print('dropped_transport_duplicate_sha256=' +
      hashlib.sha256(dropped.encode()).hexdigest())
print(f'decoded_xz_bytes={len(payload)}')
print('decoded_xz_sha256=' + hashlib.sha256(payload).hexdigest())
Path('MillenniumBraidEverything.lean.xz').write_bytes(payload)
Path('source-recovery-certificate.txt').write_text(
    f'cut={cut}\n'
    f'dropped_length={len(dropped)}\n'
    f'dropped_sha256={hashlib.sha256(dropped.encode()).hexdigest()}\n'
    f'payload_bytes={len(payload)}\n'
    f'payload_sha256={hashlib.sha256(payload).hexdigest()}\n'
)
PY

echo '52ec1001a3ee33b33e0ad1c1a024d572396850dd3c6a926299da45a6b2664578  MillenniumBraidEverything.lean.xz' \
  | sha256sum --check --strict

test "$(wc -c < MillenniumBraidEverything.lean.xz | tr -d ' ')" = '83372'

xz --decompress --stdout MillenniumBraidEverything.lean.xz \
  > MillenniumBraidEverything.lean

echo '0b5991423ffce0f4c55ece074d530ba0dd50c132b3de8698d3bb1de55257327c  MillenniumBraidEverything.lean' \
  | sha256sum --check --strict

test "$(wc -c < MillenniumBraidEverything.lean | tr -d ' ')" = '681395'
test "$(wc -l < MillenniumBraidEverything.lean | tr -d ' ')" = '9963'
test "$(grep -c '^#print axioms ' MillenniumBraidEverything.lean)" = '832'

echo 'source_reconstruction=PASS'
sha256sum MillenniumBraidEverything.lean.xz MillenniumBraidEverything.lean
wc -c -l MillenniumBraidEverything.lean.xz MillenniumBraidEverything.lean
