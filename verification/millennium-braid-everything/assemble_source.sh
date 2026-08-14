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
  sha256sum --check --strict SHA256SUMS
  wc -c part-*.b64
)

cat "${PARTS[@]}" \
  | tr -d '\n\r\t ' \
  | base64 --decode \
  > MillenniumBraidEverything.lean.xz

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
