#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, re, subprocess
from pathlib import Path

DECL_RE=re.compile(r"^\s*(?:Theorem|Proposition|Lemma|Corollary|Definition|Assumption|Hypothesis|Standard Input|External Input|Input Register|Main Theorem)\b",re.I)
SECTION_RE=re.compile(r"^\s*(?:(?:[0-9]+(?:\.[0-9]+)*)|(?:Appendix\s+[A-Z])|(?:§+\s*[0-9]+))[.)]?\s+[A-Z].{2,120}$")
PHRASES=["standard-input register","external-input boundary","first-crossing","backward shooting","Karcher","right inverse","invariant graph","background coupling","BPHZL","Reisz","Haar pivot","one-pivot","multipivot","conditional reference","replica-BKAR","boundary-to-center","exponential clustering","physical exponential","reflection positivity","O(4)","rotation defect","dimension-four","Osterwalder","Hamiltonian gap","nontrivial","spectral mass","uniform in the cutoff","uniform in the volume","directed limit"]

def win(lines,i,b=1,a=7): return "\n".join(lines[max(0,i-b):min(len(lines),i+a+1)]).strip()
def uniq(rows,lim):
    out=[];seen=set()
    for lab,val in rows:
        key=re.sub(r"\s+"," ",val).strip()
        if key and key not in seen:
            seen.add(key);out.append((lab,val))
            if len(out)>=lim:break
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--pdf',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);A=ap.parse_args()
    txt=A.pdf.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(A.pdf),str(txt)],check=True)
    text=txt.read_text(errors='replace');pages=text.split('\f')
    secs=[];decl=[];ass=[];hits=[]
    for p,page in enumerate(pages,1):
        lines=[x.rstrip() for x in page.splitlines()]
        for i,line in enumerate(lines):
            s=line.strip();lo=s.lower()
            if not s:continue
            if SECTION_RE.match(s):secs.append((f'p.{p}',s))
            if DECL_RE.match(s):decl.append((f'p.{p}',win(lines,i,0,10)))
            if any(q in lo for q in ('assume','assumption','hypothesis','standard input','external input')):ass.append((f'p.{p}',win(lines,i,1,7)))
            for q in PHRASES:
                if q.lower() in lo:hits.append((f'p.{p} · {q}',win(lines,i,2,9)));break
    secs,decl,ass,hits=uniq(secs,260),uniq(decl,200),uniq(ass,140),uniq(hits,220)
    raw=A.pdf.read_bytes();parts=['# Kirk v4 bounded structural report','',f'- bytes `{len(raw)}`',f'- sha256 `{hashlib.sha256(raw).hexdigest()}`',f'- pages `{len(pages)}`',f'- text lines `{len(text.splitlines())}`','', '> Structural extraction only; no automatic mathematical verdict.']
    def emit(title,rows):
        parts.extend(['',f'## {title}',''])
        for lab,val in rows:parts.extend([f'### {lab}','','```text',val[:2600],'```'])
    emit('Section map',secs);emit('Declarations',decl);emit('Assumption/input windows',ass);emit('Load-bearing phrase windows',hits)
    report='\n'.join(parts);A.out.write_text(report)
    print(f'KIRK_V4_EXTRACT_PASS pdf_bytes={len(raw)} pages={len(pages)} report_chars={len(report)}')
if __name__=='__main__':main()
