#!/usr/bin/env python3
"""Public finite regression for RH B42. Numerical evidence only; not RH."""
from __future__ import annotations
import cmath, math
from typing import Callable

DELTA, GAMMA, ETA, PHI, A = 0.2, 3.0, 0.25, 0.3, 0.7
Z = complex(DELTA, GAMMA)
H = math.log(2.0) / 16.0
R = 8.0 * H


def bspline7(x: float, d: int = 0) -> float:
    p = 7 - d
    return sum(((-1.0) ** k) * math.comb(8, k) * max(x-k, 0.0) ** p
               for k in range(9)) / math.factorial(p)


def k8(u: float, d: int = 0) -> float:
    x = (u + 8*H)/(2*H)
    return 0.0 if x <= 0 or x >= 8 else bspline7(x, d)/(2*H)**(d+1)


def qh(u: float) -> float:
    return -k8(u, 2) + 0.25*k8(u)


def Qh(s: complex) -> complex:
    return (0.25-s*s)*(cmath.sinh(H*s)/(H*s))**8


def chi(r: float) -> float:
    if r <= 0: return 0.0
    if r >= 1: return 1.0
    x, y = math.exp(-1/r), math.exp(-1/(1-r))
    return x/(x+y)


def m(r: float) -> float:
    return math.exp(r/2) + ETA*chi(r)*math.exp(DELTA*r)*math.cos(GAMMA*r+PHI)


def gauss(a: float, u: float) -> float:
    return math.exp(-u*u/(4*a))/math.sqrt(4*math.pi*a)


def qgauss(a: float, u: float) -> float:
    return (a*a+2*a-u*u)/(4*a*a)*gauss(a,u)


def simpson(f: Callable[[float], float], lo: float, hi: float, n: int) -> float:
    assert n > 0 and n % 2 == 0
    h = (hi-lo)/n
    s = f(lo)+f(hi)
    for j in range(1,n): s += (4 if j%2 else 2)*f(lo+j*h)
    return s*h/3


def compact_exact(t: float) -> float:
    return ETA*(cmath.exp(1j*PHI)*Qh(Z)*cmath.exp(Z*t)).real


def compact_numeric(t: float) -> float:
    return simpson(lambda u: qh(u)*(math.exp((t-u)/2)+ETA*math.exp(DELTA*(t-u))*math.cos(GAMMA*(t-u)+PHI)), -R, R, 80000)


def gaussian_numeric(t: float) -> tuple[float,float]:
    lo, hi, n = -30.0, t+15*math.sqrt(A)+5, 240000
    return (simpson(lambda r: gauss(A,t-r)*m(r),lo,hi,n),
            simpson(lambda r: qgauss(A,t-r)*m(r),lo,hi,n))


def gaussian_full(t: float) -> tuple[float,float]:
    mode=cmath.exp(1j*PHI+Z*t+A*Z*Z)
    return math.exp(t/2+A/4)+ETA*mode.real, ETA*((0.25-Z*Z)*mode).real


def cell_mass(n:int)->float:
    lo,hi=math.log(n),math.log(n+1)
    return (2*(math.exp(hi/2)-math.exp(lo/2))+
            ETA*(cmath.exp(1j*PHI)*(cmath.exp(Z*hi)-cmath.exp(Z*lo))/Z).real)


def discrete(t:float)->float:
    n0=max(3,int(math.floor(math.exp(t-R)))-2)
    n1=int(math.ceil(math.exp(t+R)))+2
    return sum(cell_mass(n)*qh(t-math.log(n)) for n in range(n0,n1+1)
               if -R <= t-math.log(n) <= R)


def main()->None:
    floor=min(m(j/100)/math.exp((j/100)/2) for j in range(-500,3001))
    assert floor >= 1-ETA-1e-13
    for t in (2.0,4.0,8.0):
        err=abs(compact_numeric(t)-compact_exact(t))
        assert err < 3e-7, (t,err)
    gerrs=[]; perrs=[]
    for t in (4.0,8.0,12.0):
        gn,pn=gaussian_numeric(t); gf,pf=gaussian_full(t)
        gerrs.append(abs(gn-gf)); perrs.append(abs(pn-pf))
    assert gerrs[2] < gerrs[1] < gerrs[0]
    assert perrs[2] < perrs[1] < perrs[0]
    scaled=[]
    for t in (8.0,12.0):
        scaled.append(abs(discrete(t)-compact_exact(t))*math.exp(t/2))
    assert max(scaled) < 0.2, scaled
    print('PASS RH B42 public finite regression')
    print('positivity ratio floor',format(floor,'.12f'))
    print('Gaussian mass errors',*[format(x,'.6e') for x in gerrs])
    print('Gaussian channel errors',*[format(x,'.6e') for x in perrs])
    print('scaled lattice errors',*[format(x,'.6e') for x in scaled])
    print('HONESTY numerical regression only; no prime estimate or RH theorem')

if __name__=='__main__': main()
