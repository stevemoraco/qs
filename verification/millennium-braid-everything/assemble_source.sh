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
clean = []
for part in parts:
    text = ''.join(ch for ch in Path(part).read_text() if not ch.isspace())
    bad = [(i, ch) for i, ch in enumerate(text) if ch not in alphabet]
    if bad:
        raise SystemExit(f'{part}: invalid base64 characters: {bad[:20]}')
    clean.append(text)
    print(f'{part}: clean={len(text)} mod4={len(text)%4}')

# The shard plan was 8,000 characters per elementary shard.  The transported
# part-02 contains 9,861 characters while part-03 starts at the next 8,000-byte
# boundary.  Retain the first 8,000 characters and record the 1,861-character
# overlap tail.  The decompressed Lean source hash below, not this structural
# inference, is the final authority.
assert [len(x) for x in clean] == [8000, 8000, 9861, 8000, 8000,
                                  16000, 16000, 16000, 16000, 7164]
dropped = clean[2][8000:]
clean[2] = clean[2][:8000]
joined = ''.join(clean)
assert len(joined) == 111164
assert len(joined) % 4 == 0
payload = base64.b64decode(joined, validate=True)
Path('MillenniumBraidEverything.lean.xz').write_bytes(payload)
Path('source-recovery-certificate.txt').write_text(
    'repair=retain_first_8000_characters_of_part_02\n'
    f'dropped_length={len(dropped)}\n'
    f'dropped_sha256={hashlib.sha256(dropped.encode()).hexdigest()}\n'
    f'payload_bytes={len(payload)}\n'
    f'payload_sha256={hashlib.sha256(payload).hexdigest()}\n'
)
print(f'dropped_transport_overlap_length={len(dropped)}')
print('dropped_transport_overlap_sha256=' + hashlib.sha256(dropped.encode()).hexdigest())
print(f'decoded_xz_bytes={len(payload)}')
print('decoded_xz_sha256=' + hashlib.sha256(payload).hexdigest())
PY

test "$(wc -c < MillenniumBraidEverything.lean.xz | tr -d ' ')" = '83372'

# Do not let a stale compressed-container digest hide a valid exact source.
# First require XZ stream integrity, then compare the decompressed source to the
# independently pinned Lean-source digest and exact structural counts.
xz --test MillenniumBraidEverything.lean.xz
xz --decompress --stdout MillenniumBraidEverything.lean.xz \
  > MillenniumBraidEverything.lean

sha256sum MillenniumBraidEverything.lean.xz MillenniumBraidEverything.lean

echo '0b5991423ffce0f4c55ece074d530ba0dd50c132b3de8698d3bb1de55257327c  MillenniumBraidEverything.lean' \
  | sha256sum --check --strict

test "$(wc -c < MillenniumBraidEverything.lean | tr -d ' ')" = '681395'
test "$(wc -l < MillenniumBraidEverything.lean | tr -d ' ')" = '9963'
test "$(grep -c '^#print axioms ' MillenniumBraidEverything.lean)" = '832'

echo 'source_reconstruction=PASS'
wc -c -l MillenniumBraidEverything.lean.xz MillenniumBraidEverything.lean
