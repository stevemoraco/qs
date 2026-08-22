#!/usr/bin/env python3
"""Exact finite regression for the random marker-selector theorem.

Numerical/combinatorial regression only: not a uniform selector and not P != NP.
"""
from __future__ import annotations
import itertools, math, random
from fractions import Fraction


def pairs(n:int): return list(itertools.combinations(range(n),2))
def quads(n:int): return list(itertools.combinations(range(n),4))
def completions(n:int,p:tuple[int,int]):
    forbidden=set(p)
    return list(itertools.combinations([i for i in range(n) if i not in forbidden],2))

def log_circuits(n:int,g:int)->float:
    return math.log2(g+1)+math.log2(n+g+2)+g*(4+2*math.log2(n+g+2))

def incidence()->int:
    rng=random.Random(0x504E5053454C4543); cases=0
    for n in range(4,21):
        ps,qs=pairs(n),quads(n); qset=set(qs); d=math.comb(n-2,2)
        for numerator in (1,2,3,5,7):
            accepted={q for q in qs if rng.randrange(11)<numerator}
            total=0; density=Fraction(0,1)
            for p in ps:
                count=0
                for a in completions(n,p):
                    q=tuple(sorted((*p,*a))); assert q in qset
                    count+=int(q in accepted)
                total+=count; density+=Fraction(count,d)
            assert total==6*len(accepted)
            assert density/len(ps)==Fraction(len(accepted),len(qs))
            cases+=1
    return cases

def main()->None:
    cases=incidence(); fp=0
    for n in range(10,500):
        W=math.comb(n,4); N=math.comb(n,2); assert N<=W//4
        for S in {0,1,N,max(0,N-1)}:
            assert (Fraction(3*W,4)-S)/(W-S)>=Fraction(2,3); fp+=1
    rows=[]
    for n in (128,192,256,512,1024,2048,4096,8192):
        g=int(n*n/(128*math.log2(n)))
        margin=math.comb(n,2)*math.log2(4/3)-log_circuits(n,g)
        assert margin>0; rows.append((n,g,margin))
    print('PASS PNP random-selector finite regression')
    print('exact incidence families',cases)
    print('false-positive ledgers',fp)
    for n,g,margin in rows:
        print(f'n={n} g={g} union_bound_margin_bits={margin:.6f}')
    print('HONESTY finite regression only; no uniform NP selector or P != NP proof')

if __name__=='__main__': main()
