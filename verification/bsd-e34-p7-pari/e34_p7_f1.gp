\\ E34,p=7 selected DMM second-stage backend: certify F1=Q(i,delta), delta=7 eta, eta^2=alpha.
\\ Exact polynomial operations plus bnfinit/bnfcertify.
default(parisizemax, 16000000000);
x='x;
g = x^12 - 308*x^11 - 20678*x^10 + 972748*x^9 - 12084233*x^8
    + 197515864*x^7 - 1880972212*x^6 + 4961023032*x^5
    + 12907389439*x^4 - 85065403556*x^3 + 52540396314*x^2
    - 55365148804*x - 1977326743;
hD = 7^12 * subst(g, x, x^2/7);
if(poldegree(hD) != 24, error("bad hD degree"));
if(denominator(content(hD)) != 1, error("hD not integral"));
print("E34_P7_F1_HD_DEGREE=", poldegree(hD));
print("E34_P7_F1_HD_IRREDUCIBLE=", polisirreducible(hD));
cv = polcompositum(hD, x^2+1);
print("E34_P7_F1_COMPOSITA=", #cv);
if(#cv != 1, error("unexpected F1 compositum decomposition"));
p = cv[1];
print("E34_P7_F1_RAW_DEGREE=", poldegree(p));
if(poldegree(p) != 48, error("bad F1 degree"));
p = polredbest(p);
print("E34_P7_F1_POLRED_DEGREE=", poldegree(p));
print("E34_P7_F1_POL=", p);
bnf = bnfinit(p, 1);
print("E34_P7_F1_BNFINIT_DONE=1");
cert = bnfcertify(bnf);
print("E34_P7_F1_BNFCERTIFY=", cert);
if(cert != 1, error("F1 bnfcertify failed"));
h = bnf.no;
cyc = bnf.cyc;
print("E34_P7_F1_CLASSNO=", h);
print("E34_P7_F1_CLASSGROUP_CYC=", cyc);
print("E34_P7_F1_V7_CLASSNO=", valuation(h,7));
print("E34_P7_F1_CERTIFIED=1");
