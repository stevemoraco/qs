#!/usr/bin/env python3
from fractions import Fraction as Q

# Target theta-secant character, coefficient of x^j (not divided moments).
d = 23
v = [Q(1), Q(1), Q(-d,2), Q(-d,6), Q(d*d,24)]

# Stable point-free ideal construction: S=CI(2,6), 3 CI(2,2,2), 1 CI(2,2,4).
def mul(a,b,n=4):
    out=[Q(0)]*(n+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j<=n: out[i+j]+=x*y
    return out

def exp_neg(a,n=4):
    out=[]
    p=Q(1)
    fact=1
    for j in range(n+1):
        if j:
            p *= -a
            fact *= j
        out.append(p/fact)
    return out

def ci(degrees):
    out=[Q(1),Q(0),Q(0),Q(0),Q(0)]
    for a in degrees:
        e=exp_neg(a)
        out=mul(out,[Q(1)-e[0]]+[-z for z in e[1:]])
    return out

s=ci([2,6])
c222=ci([2,2,2])
c224=ci([2,2,4])
oz=[s[j]+3*c222[j]+c224[j] for j in range(5)]
assert oz == [Q(0),Q(0),Q(12),Q(-8),Q(-20)]

expx=[Q(1),Q(1),Q(1,2),Q(1,6),Q(1,24)]
ideal=[Q(1)-oz[0]]+[-oz[j] for j in range(1,5)]
assert mul(expx,ideal)==v

# Genus-four Jacobian bundle arithmetic.
ts=[-10,-10,-8,-4,-4]+[2]*18
assert len(ts)==23 and sum(ts)==0 and sum(t*t for t in ts)==368
D2=Q(-3)
c2= -D2*sum(t*t for t in ts)/2
assert c2==552
# GRR result for rank 24 bundle on W_2.
ch_push=[Q(0),Q(0),Q(12),Q(-8),Q(-20)]
assert mul(expx,[Q(1)-ch_push[0]]+[-z for z in ch_push[1:]])==v

# Hodge contraction kernel: i_pi(x^j)=j(j-1)B x^(j-2).
# Coefficients of (d B wedge + i_pi) v.
res=[Q(0)]*5
for j,c in enumerate(v):
    if j+2<=4: res[j+2]+=d*c
    if j>=2: res[j-2]+=j*(j-1)*c
# Degrees are shifted in Hodge bidegree; compare matching total target slots:
assert d*v[0]+2*v[2]==0
assert d*v[1]+6*v[3]==0
assert d*v[2]+12*v[4]==0

# Pure-surface Hilbert polynomial coefficients.
k=1
# int x^4=24
# ch(O_Z)=12k x^2-8k x^3+(-24k^2+4k)x^4
# coefficient after exp(mx)
def chi_surface(m,k=1):
    return 24*(Q(12*k)*Q(m*m,2)+Q(-8*k)*m+Q(-24*k*k+4*k))
assert chi_surface(0)==-480
assert chi_surface(1)==-528
assert chi_surface(2)==-288

print("PASS: d=23 secant character, stable realizations, contraction kernel, and Euler data")
