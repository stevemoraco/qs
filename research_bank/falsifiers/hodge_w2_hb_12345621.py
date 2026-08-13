#!/usr/bin/env python3
from fractions import Fraction as F
from math import isqrt
D2,Dv,v2,c2=F(-3),F(1),F(21),F(6)
def pair(x,y):
 a,b=x;c,d=y
 return a*c*D2+(a*d+b*c)*Dv+b*d*v2
def ch2(t):
 l=(F(t,3),F(-31,3));v=(F(0),F(1))
 return F(111,2)*v2-71*c2-4*pair(v,l)+F(3,2)*pair(l,l)
for t in range(-50,51):
 assert ch2(t)==F(4971)-F(35,3)*t-F(1,2)*t*t
disc=67*67+12*33138;r=isqrt(disc)
assert disc==402145 and r==634 and r*r<disc<(r+1)*(r+1)
h=[1,2,3,4,5,6,2,1]
at=lambda i:h[i] if 0<=i<len(h) else 0
coeff={d:at(d)-2*at(d-1)+at(d-2) for d in range(len(h)+3)}
assert {d:c for d,c in coeff.items() if c}=={0:1,6:-5,7:3,9:1}
print("PASS")
