#!/usr/bin/env python3
from collections import defaultdict
from fractions import Fraction as F

def add(x,y): return tuple(a+b for a,b in zip(x,y))
def sub(x,y): return tuple(a-b for a,b in zip(x,y))
def scale(c,x): return tuple(c*a for a in x)
def dot(x,y): return sum(a*b for a,b in zip(x,y))
def cross(x,y): return (x[1]*y[2]-x[2]*y[1],x[2]*y[0]-x[0]*y[2],x[0]*y[1]-x[1]*y[0])
def leray(k,x):
    kk=dot(k,k)
    if kk==0:
        # The zero Fourier mode is not projected.  In every use below its
        # convective raw vector vanishes; assert that fact rather than divide
        # by zero or silently choose a convention.
        assert x==(0,0,0)
        return x
    return sub(x,scale(F(dot(k,x),kk),k))
def leray_num(k,x): return sub(scale(dot(k,k),x),scale(dot(k,x),k))
def bilinear(k,uk,l,ul):
    out=add(k,l)
    raw=add(scale(dot(uk,l),ul),scale(dot(ul,k),uk))
    return leray(out,raw)

q2=(1,-1,0); ell2=(-7,-7,10); h2=(-20,-20,-28)
ell6=(-14,-1,-1); h6=(-4,28,28)
a=add(ell2,h2); b=sub(ell2,h2); c=scale(-1,sub(ell6,h6))
s=add(a,c); r=sub(b,c)
ua=add(sub(scale(198,h2),scale(1584,ell2)),q2)
ub=sub(add(scale(198,h2),scale(1584,ell2)),q2)
uc=(-22968,3959,3961)
assert (a,b,c)==((-27,-27,-18),(13,13,38),(10,29,29))
assert (s,r)==((-17,2,11),(3,-16,9))
assert add(s,r)==scale(2,ell2)
assert dot(a,ua)==dot(b,ub)==dot(c,uc)==0
Bs=bilinear(a,ua,c,uc)
Br=bilinear(b,ub,scale(-1,c),uc)
Bsr=bilinear(s,Bs,r,Br)
assert dot(s,Bs)==dot(r,Br)==dot(add(s,r),Bsr)==0
assert Bs==scale(F(-48599324),(29,-67,57))
assert Br==scale(F(-1117784452,173),(725,-3,-247))
assert Bsr==scale(F(-6176372472021338295808,173),q2)
raw_s=add(scale(dot(ua,c),uc),scale(dot(uc,a),ua))
raw_r=add(scale(dot(ub,scale(-1,c)),uc),scale(dot(uc,b),ub))
Ns=leray_num(s,raw_s); Nr=leray_num(r,raw_r)
raw2=add(scale(dot(Ns,r),Nr),scale(dot(Nr,s),Ns))
assert leray_num(add(s,r),raw2)==scale(
    -4050316834212265142271787008,q2)


# Sum every ordered inviscid Picard tree contributing to the square-free
# monomial A_a A_b A_c A_{-c}.  U[n] is the coefficient of t^n and obeys
# U[n+1]=(1/(n+1))*sum_{p+q=n} Q(U[p],U[q]).
def ordered_q(k,u,l,ul):
    out=add(k,l)
    return leray(out,scale(dot(u,l),ul))

zero=(F(0),F(0),F(0))
u0=defaultdict(lambda: zero)
for i,(k,u) in enumerate(((a,ua),(b,ub),(c,uc),(scale(-1,c),uc))):
    monomial=tuple(1 if i==j else 0 for j in range(4))
    u0[(k,monomial)]=tuple(map(F,u))
picard=[u0]
for n in range(3):
    nxt=defaultdict(lambda: zero)
    for p in range(n+1):
        q=n-p
        for (k,mk),uk in picard[p].items():
            for (l,ml),ul in picard[q].items():
                monomial=tuple(x+y for x,y in zip(mk,ml))
                key=(add(k,l),monomial)
                nxt[key]=add(nxt[key],scale(F(1,n+1),ordered_q(k,uk,l,ul)))
    picard.append(nxt)

square_free=(1,1,1,1)
W=picard[3][(scale(2,ell2),square_free)]
expected_W=(
    F(-29709287450407586552369503382070768,51741447392101),
    F(11805421958679668258158519494433904,155224342176303),
    F(-54125708274780163979264993456244880,155224342176303))
assert W==expected_W
assert dot(ell2,W)==0
assert dot(q2,W)==F(
    -100933284309902427915267029640646208,155224342176303)
q2_cross_ell2=(-10,-10,-14)
assert dot(q2_cross_ell2,W)==F(
    510328106590784403233069938301737440,51741447392101)


# Full six-color polynomial under the standard restricted schedule: one real
# amplitude t_i is shared by both branches and both conjugate modes of color i.
# Keying the Picard recurrence by the exponent vector of (t_0,...,t_5)
# extracts every quartic monomial exactly.
qs=((1,1,0),(1,-1,0),(1,0,1),(1,0,-1),(0,1,1),(0,1,-1))
ells=((-1,1,14),(-7,-7,10),(1,14,-1),(-7,10,-7),(-14,1,-1),(-14,-1,-1))
full_u0=defaultdict(lambda: zero)
for i,(qi,elli) in enumerate(zip(qs,ells)):
    hi=scale(2,cross(qi,elli))
    gi=cross(elli,hi)
    ai=add(elli,hi)
    bi=sub(elli,hi)
    uai=add(sub(scale(198,hi),scale(1584,elli)),gi)
    ubi=sub(add(scale(198,hi),scale(1584,elli)),gi)
    monomial=tuple(1 if i==j else 0 for j in range(6))
    for reality in (1,-1):
        full_u0[(scale(reality,ai),monomial)]=tuple(map(F,uai))
        full_u0[(scale(reality,bi),monomial)]=tuple(map(F,ubi))

full_picard=[full_u0]
for n in range(3):
    nxt=defaultdict(lambda: zero)
    for p in range(n+1):
        q=n-p
        for (k,mk),uk in full_picard[p].items():
            for (l,ml),ul in full_picard[q].items():
                monomial=tuple(x+y for x,y in zip(mk,ml))
                key=(add(k,l),monomial)
                nxt[key]=add(nxt[key],scale(F(1,n+1),ordered_q(k,uk,l,ul)))
    full_picard.append(nxt)

target5=scale(2,ells[5])
off5=cross(qs[5],ells[5])
color5_terms={
    monomial: dot(off5,coefficient)
    for (frequency,monomial),coefficient in full_picard[3].items()
    if frequency==target5 and coefficient != zero
}
expected_color5_monomials={
    (0,0,0,0,0,4),
    (0,0,0,0,2,2),
    (0,0,0,2,0,2),
    (0,0,2,0,0,2),
    (0,2,0,0,0,2),
    (1,1,0,0,1,1),
    (2,0,0,0,0,2),
}
assert set(color5_terms)==expected_color5_monomials
assert color5_terms[(0,0,0,0,0,4)]==0
assert all(value < 0 for monomial,value in color5_terms.items()
           if monomial != (0,0,0,0,0,4))
# Therefore the off-target component is strictly negative whenever every
# shared real color amplitude t_i is positive.  This sign conclusion is
# restricted to this six-parameter schedule; independent branch phases are
# not covered.
print('s',s,'normSq',dot(s,s),'B_s',Bs)
print('r',r,'normSq',dot(r,r),'B_r',Br)
print('return',add(s,r),'B_sr',Bsr)
print('all ordered quartic Picard trees',W)
print('color-5 off-target quartic signs',color5_terms)
