#!/usr/bin/env python3
import argparse,hashlib,json,pathlib,re,subprocess
from collections import defaultdict
P=('Mathlib','Lean','Init','Std','Batteries','Qq','Aesop');I=re.compile(r'^\s*import\s+([^\n]+)$',re.M)
def g(r,*a):
 p=subprocess.run(['git','-C',str(r),*a],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 if p.returncode:raise RuntimeError(p.stdout)
 return p.stdout
def clean(s):
 o=[];i=0;n=len(s);b=0;l=False;q=False;e=False
 while i<n:
  c=s[i];d=s[i+1]if i+1<n else''
  if l:o.append('\n'if c=='\n'else' ');l=c!='\n';i+=1;continue
  if b:
   if c=='/'and d=='-':b+=1;o+=[' ',' '];i+=2
   elif c=='-'and d=='/':b-=1;o+=[' ',' '];i+=2
   else:o.append('\n'if c=='\n'else' ');i+=1
   continue
  if q:
   o.append('\n'if c=='\n'else' ')
   if e:e=False
   elif c=='\\':e=True
   elif c=='"':q=False
   i+=1;continue
  if c=='-'and d=='-':l=True;o+=[' ',' '];i+=2
  elif c=='/'and d=='-':b=1;o+=[' ',' '];i+=2
  elif c=='"':q=True;o.append(' ');i+=1
  else:o.append(c);i+=1
 return''.join(o)
def alone(s):
 for m in I.finditer(clean(s)):
  for t in m.group(1).split('--',1)[0].split():
   if not(t in P or t.startswith(tuple(x+'.'for x in P))):return False
 return True
def main():
 a=argparse.ArgumentParser();a.add_argument('--repo',type=pathlib.Path,required=True);a.add_argument('--out',type=pathlib.Path,required=True);a.add_argument('--label',required=True);z=a.parse_args();refs=['HEAD']+[x for x in g(z.repo,'for-each-ref','--format=%(refname)','refs/heads','refs/remotes').splitlines()if x and not x.endswith('/HEAD')];trees=set();texts={};loc=defaultdict(list);rows=[]
 for r in refs:
  try:c=g(z.repo,'rev-parse',f'{r}^{{commit}}').strip();t=g(z.repo,'rev-parse',f'{r}^{{tree}}').strip()
  except Exception as e:rows.append({'ref':r,'error':str(e)});continue
  if t in trees:rows.append({'ref':r,'commit':c,'tree':t,'duplicate_tree':True});continue
  trees.add(t);n=0
  for p in g(z.repo,'ls-tree','-r','--name-only',r).splitlines():
   if not p.endswith('.lean')or p.startswith(('verification/unified-public-bank/','.lake/')):continue
   try:x=g(z.repo,'ls-tree',r,'--',p).split();b=x[2];s=g(z.repo,'show',f'{r}:{p}')
   except Exception:continue
   if not alone(s):continue
   h=hashlib.sha256(s.encode()).hexdigest();texts.setdefault(h,s);loc[h].append({'ref':r,'commit':c,'path':p,'blob':b});n+=1
  rows.append({'ref':r,'commit':c,'tree':t,'standalone_instances':n})
 z.out.mkdir(parents=True,exist_ok=True);src=[]
 for h,s in sorted(texts.items()):
  f=z.out/f'{z.label}_{h[:16]}.lean';f.write_text(s);src.append({'sha256':h,'file':f.name,'locations':loc[h]})
 (z.out/f'{z.label}_REF_MANIFEST.json').write_text(json.dumps({'label':z.label,'unique_sources':len(src),'refs':rows,'sources':src},indent=2));print(len(src))
if __name__=='__main__':main()
