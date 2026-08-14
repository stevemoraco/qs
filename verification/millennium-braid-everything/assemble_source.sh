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

# Failed hosted reconstruction isolated exactly one malformed shard.  The
# intended shard schedule has five 8,000-character shards, four combined
# 16,000-character shards, and one 7,164-character tail.  part-02 contains the
# correct 8,000-character shard followed by an accidental 1,861-character
# duplicate tail.  We drop only that tail, record its digest, and then require
# the reconstructed compressed payload and Lean source to match their original
# independently pinned hashes below.  A wrong repair cannot pass those hashes.
assert len(clean_parts[0]) == 8000
assert len(clean_parts[1]) == 8000
assert len(clean_parts[2]) == 9861
assert len(clean_parts[3]) == 8000
assert len(clean_parts[4]) == 8000
assert all(len(clean_parts[i]) == 16000 for i in range(5, 9))
assert len(clean_parts[9]) == 7164

part02_prefix = clean_parts[2][:8000]
part02_extra = clean_parts[2][8000:]
print(f'part-02 retained_length={len(part02_prefix)}')
print(f'part-02 dropped_duplicate_tail_length={len(part02_extra)}')
print('part-02 dropped_duplicate_tail_sha256=' +
      hashlib.sha256(part02_extra.encode()).hexdigest())
clean_parts[2] = part02_prefix

joined = ''.join(clean_parts)
print(f'joined_clean_length={len(joined)} mod4={len(joined)%4}')
assert len(joined) == 111164
assert len(joined) % 4 == 0
payload = base64.b64decode(joined, validate=True)
Path('MillenniumBraidEverything.lean.xz').write_bytes(payload)
print(f'decoded_xz_bytes={len(payload)}')
print('decoded_xz_sha256=' + hashlib.sha256(payload).hexdigest())
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
