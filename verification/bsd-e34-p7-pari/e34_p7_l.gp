\\ E34,p=7 selected DMM quartic field backend: certify L=Q(i,gamma), gamma=7 beta.
default(parisizemax, 24000000000);
x='x;
g = x^12 - 308*x^11 - 20678*x^10 + 972748*x^9 - 12084233*x^8
    + 197515864*x^7 - 1880972212*x^6 + 4961023032*x^5
    + 12907389439*x^4 - 85065403556*x^3 + 52540396314*x^2
    - 55365148804*x - 1977326743;
hD = 7^12 * subst(g, x, x^2/7);
if(poldegree(hD) != 24, error("bad hD degree"));
if(denominator(content(hD)) != 1, error("hD not integral"));
hG = 238^24 * subst(hD, x, x^2/238);
if(poldegree(hG) != 48, error("bad hG degree"));
if(denominator(content(hG)) != 1, error("hG not integral"));
print("E34_P7_L_HG_DEGREE=", poldegree(hG));
print("E34_P7_L_HG_IRREDUCIBLE=", polisirreducible(hG));
cv = polcompositum(hG, x^2+1);
print("E34_P7_L_COMPOSITA=", #cv);
if(#cv != 1, error("unexpected L compositum decomposition"));
p = cv[1];
print("E34_P7_L_RAW_DEGREE=", poldegree(p));
if(poldegree(p) != 96, error("bad L degree"));
p = polredbest(p);
print("E34_P7_L_POLRED_DEGREE=", poldegree(p));
print("E34_P7_L_POL=", p);
bnf = bnfinit(p, 1);
print("E34_P7_L_BNFINIT_DONE=1");
cert = bnfcertify(bnf);
print("E34_P7_L_BNFCERTIFY=", cert);
if(cert != 1, error("L bnfcertify failed"));
h = bnf.no;
cyc = bnf.cyc;
print("E34_P7_L_CLASSNO=", h);
print("E34_P7_L_CLASSGROUP_CYC=", cyc);
print("E34_P7_L_V7_CLASSNO=", valuation(h,7));
print("E34_P7_L_CERTIFIED=1");
