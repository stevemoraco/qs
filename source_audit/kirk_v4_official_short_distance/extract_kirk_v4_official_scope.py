#!/usr/bin/env python3
from __future__ import annotations

import json
import pathlib
import re

TEXT = pathlib.Path('kirk-v4.txt')
text = TEXT.read_text(errors='replace')
lines = text.splitlines()

patterns = {
    'theorem_1_1': r'Theorem\s+1\.1',
    'theorem_10_4': r'Theorem\s+10\.4',
    'theorem_11_1': r'Theorem\s+11\.1',
    'operator_product': r'operator\s+product',
    'ope_token': r'\bOPE\b',
    'short_distance': r'short[- ]distance',
    'asymptotic_freedom': r'asymptotic\s+freedom',
    'curvature_jet': r'curvature[- ]jet',
    'local_quantum_field': r'local\s+quantum\s+field',
    'stress_tensor': r'stress[- ](?:energy|tensor)',
    'composite_operator': r'composite\s+operator',
    'bphzl': r'BPHZL',
    'nonexceptional_momentum': r'nonexceptional\s+(?:external\s+)?momentum',
    'renormalization_group': r'renormalization\s+group',
    'j_a_f_f_e_witten': r'Jaffe\s+and\s+E\.\s+Witten',
}

out_dir = pathlib.Path('extracted')
out_dir.mkdir(exist_ok=True)
summary: dict[str, object] = {
    'line_count': len(lines),
    'patterns': {},
}

for name, pattern in patterns.items():
    rx = re.compile(pattern, re.I)
    hits = [i for i, line in enumerate(lines) if rx.search(line)]
    summary['patterns'][name] = {
        'pattern': pattern,
        'hit_count': len(hits),
        'line_numbers_1_based': [i + 1 for i in hits],
    }
    chunks = []
    for j, i in enumerate(hits):
        lo = max(0, i - 12)
        hi = min(len(lines), i + 40)
        chunks.append(
            f'=== {name} hit {j + 1}; line {i + 1}; context {lo + 1}-{hi} ===\n'
            + '\n'.join(lines[lo:hi])
            + '\n'
        )
    (out_dir / f'{name}.txt').write_text('\n'.join(chunks))

# Preserve exact early pages and terminal completion pages for theorem/scope replay.
(out_dir / 'opening_1_1200.txt').write_text('\n'.join(lines[:1200]) + '\n')
(out_dir / 'terminal_30000_end.txt').write_text('\n'.join(lines[30000:]) + '\n')
pathlib.Path('official-scope-summary.json').write_text(
    json.dumps(summary, indent=2, sort_keys=True) + '\n'
)
print(json.dumps(summary, indent=2, sort_keys=True))
