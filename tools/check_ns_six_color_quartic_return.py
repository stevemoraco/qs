#!/usr/bin/env python3
from fractions import Fraction as F

def add(x,y): return tuple(a+b for a,b in zip(x,y))
def sub(x,y): return tuple(a-b for a,b in zip(x,y))
def scale(c,x): return tuple(c*a for a in x)
def dot(x,y): return sum(a*b for a,b in zip(x,y))
def leray(k,x): return sub(x,scale(F(dot(k,x),dot(k,k)),k))
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
print('s',s,'normSq',dot(s,s),'B_s',Bs)
print('r',r,'normSq',dot(r,r),'B_r',Br)
print('return',add(s,r),'B_sr',Bsr)
