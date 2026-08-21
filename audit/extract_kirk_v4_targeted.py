#!/usr/bin/env python3
from __future__ import annotations
import argparse, subprocess
from pathlib import Path

RANGES=[
    (3,5,'theorem-boundary-and-external-inputs'),
    (5,10,'karcher-block-folded-symbol-and-normal-chart'),
    (23,52,'weak-rg-invariant-graph-and-coefficient'),
    (52,72,'directed-handoff-and-haar-optical-matching'),
    (72,95,'ward-o4-os-gap-and-nontriviality'),
    (95,111,'appendix-a-endpoint-noncollapse-and-supporting-appendices'),
    (112,115,'bibliography'),
]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--pdf',type=Path,required=True);ap.add_argument('--outdir',type=Path,required=True);a=ap.parse_args()
    a.outdir.mkdir(parents=True,exist_ok=True)
    total=0
    for lo,hi,name in RANGES:
        out=a.outdir/f'{lo:03d}-{hi:03d}-{name}.txt'
        subprocess.run(['pdftotext','-f',str(lo),'-l',str(hi),'-layout',str(a.pdf),str(out)],check=True)
        text=out.read_text(errors='replace')
        total+=len(text)
        print(f'TARGET_RANGE {lo}-{hi} chars={len(text)} file={out.name}')
    print(f'KIRK_V4_TARGETED_PASS chars={total}')
if __name__=='__main__':main()
