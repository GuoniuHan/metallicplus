# UNIFORM (all n,j) certificate for Steps 1 and 2 of Algorithm NextABC,
# (condition (S12) of Corollary 3.2 and Proposition 3.3 of the paper) by the
# POLYNOMIALITY CRITERION (Lemma 3.1):
#
#   Let (A,B,C) satisfy (3.4): A,B,C in QQ[q], B(0)=1, C(0)=0; let a!=0, and
#   let (k,D) satisfy (3.5): k>=0, D in QQ[q], D(0)=1, deg D <= k+1; and let A*,B*,C* be given by Step 3.
#   Then (k,a,D) is the output of Steps 1,2 of NextABC(A,B,C)
#   IFF  A*, B* are polynomials and B*(0)=1.
#
# So for every tuple (A,B,C;K,D) of the pass-tables we prove, on a cone of
# (n,j), the four facts
#   (i)   (A,B,C) satisfies (3.4);
#   (ii)  (3.5): k >= 0, D(0)=1, deg_q D <= k+1   (K = a q^k);
#   (iii) the Step-3 image (A*,B*) is polynomial with B*(0)=1;
# and check that the sequence uses the tuple only inside that cone (coverage).
#
# Each entry X is a rational function of q, u=q^{2j}, w=q^n whose denominator
# is lambda q^s (q-1)^e u^b w^c.  "Polynomial" is proved in two parts:
#   (a) (q-1)^e divides the numerator under u=q^{2j}, w=q^n IDENTICALLY in
#       (j,n): expand at q=1+eps with j,n symbolic (binomial series) -- so X
#       is a Laurent polynomial in q for every (n,j);
#   (b) X has no negative power of q: write X = sum_{(b,c)} P_{b,c}(q) u^b w^c;
#       the term (b,c) has q-order val_q P_{b,c} + 2jb + nc, an AFFINE
#       function of (j,n), and we require it >= 0 on the cone
#           C(j0,d0) = { j >= j0 ,  n-2j >= d0 }     (d0 is called N in the code).
# "affine g >= target on C" is a finite check, eq. (3.9) of the paper: with
# j=j0+s, n-2j=d0+s' (s,s'>=0), g = G0 + Gs s + Gt s', and g>=target on C iff
# Gs,Gt>=0, G0>=target.
# Everything below is exact; no value of n or j is ever substituted.
import sys, os
_o=sys.stdout; sys.stdout=open(os.devnull,'w')
load('passtables.sage')                 # dicts gp1,gp2,go2,s1,s2,o2,br; Fs,qs,u,w
sys.stdout=_o
Pq = PolynomialRing(QQ,'qs'); (qP,) = Pq.gens()
Fq = Pq.fraction_field()

def blocks(elt):
    """X -> dict {(b,c): P_{b,c} in Fq}."""
    e = Fs(elt); num = e.numerator(); den = e.denominator()
    du, dw = den.degree(u), den.degree(w)
    denq = den // (u^du * w^dw)
    assert denq*(u^du*w^dw) == den and denq.degree(u)==0 and denq.degree(w)==0, \
        "denominator not (q-poly)*u^a*w^b : %s" % den
    denP = Pq(denq.subs({u:1, w:1}))
    out = {}
    for (eq, eu, ew), c in num.dict().items():
        key = (eu-du, ew-dw)
        out[key] = out.get(key, Pq(0)) + QQ(c)*qP^eq
    return { k: Fq(v)/Fq(denP) for k,v in out.items() if v != 0 }

def qval(r): return r.numerator().valuation() - r.denominator().valuation()
def qlc(r):
    num, den = r.numerator(), r.denominator()
    return num[num.valuation()] / den[den.valuation()]
def affine(bc, val):                      # order of block bc: val + 2b*j + c*n
    b, c = bc
    return {'Cj': 2*b, 'Cn': c, 'K': val}
def ge_on_cone(coef, target, j0, N):
    """True iff  K + Cj*j + Cn*n >= target  for all (j,n) in C(j0,N)."""
    Cj, Cn, K = coef['Cj'], coef['Cn'], coef['K']
    G0 = K + Cj*j0 + Cn*(2*j0+N)
    return (Cj + 2*Cn >= 0) and (Cn >= 0) and (G0 >= target)

def split_K(K):
    """K = a q^{k0} u^{b0} w^{c0}  ->  (a, (b0,c0), k0)."""
    bl = blocks(K); assert len(bl)==1, "K not a monomial-block: %s"%K
    (bc, P), = bl.items(); v = qval(P)
    assert P == qlc(P)*qP^v, "K coeff not a monomial in q: %s"%P
    return qlc(P), bc, v

def kstr(k0,bc0):
    b,c=bc0; parts=[]
    if c: parts.append("n" if c==1 else "%d*n"%c)
    if b: parts.append(("+" if b>0 else "")+("-2j" if b==-1 else "2j" if b==1 else "%d*2j"%b))
    if k0 or not parts: parts.append(("%+d"%k0) if parts else str(k0))
    return "".join(parts).lstrip("+") or "0"
def pp(e): return str(e).replace('qs','q').replace('w','q^n').replace('u','q^{2j}')

# ---- (a) the (q-1)-factor of the denominator cancels, identically in (j,n) ----
JN = PolynomialRing(QQ, ['J','Nn']); Jv, Nv = JN.gens()
Tt = PolynomialRing(JN, 't'); (tt,) = Tt.gens()
def _binser(top, e):                      # (1+t)^top mod t^e, top symbolic
    s = Tt(0); c = JN(1)
    for i in range(e):
        s += c*tt^i; c = c*(top - i)/(i+1)
    return s
def qm1_ok(elt):
    e = Fs(elt); num, den = e.numerator(), e.denominator()
    denq = Pq((den // (u^den.degree(u)*w^den.degree(w))).subs({u:1,w:1}))
    mult = 0; rest = denq
    while rest(1) == 0: rest = rest // (qP-1); mult += 1
    rest = rest // qP^rest.valuation()
    assert rest.degree() == 0, "unexpected denominator factor %s" % denq
    if mult == 0: return True
    U, W = _binser(2*Jv, mult), _binser(Nv, mult)
    val = Tt(0)
    for (eq,eu,ew), c in num.dict().items():
        val += QQ(c)*(1+tt)^eq * U^eu * W^ew
    return all(val[i] == 0 for i in range(mult))

# ---- (b) block tests on a cone ------------------------------------------------
def order_ge(X, tgt, j0, N):              # every block of X has q-order >= tgt
    return all(ge_on_cone(affine(bc,qval(P)), tgt, j0, N) for bc,P in blocks(X).items())
def is_one_plus(X, j0, N):                # X = 1 + O(q): block 1 starts with 1, rest >= 1
    bl = blocks(X)
    if (0,0) not in bl or qval(bl[(0,0)]) != 0 or qlc(bl[(0,0)]) != 1: return False
    return all(ge_on_cone(affine(bc,qval(P)), 1, j0, N) for bc,P in bl.items() if bc != (0,0))

def cond26(A,B,C, j0, N):             # (i): A,B,C polynomials, B(0)=1, C(0)=0
    return (all(qm1_ok(X) for X in (A,B,C)) and order_ge(A,0,j0,N)
            and is_one_plus(B,j0,N) and order_ge(C,1,j0,N))

def kD_ok(K, D, j0, N):                   # (ii): k>=0, D polynomial, D(0)=1, deg D<=k+1
    a, bc0, k0 = split_K(K)
    if not ge_on_cone(affine(bc0,k0), 0, j0, N): return False
    if not (qm1_ok(D) and is_one_plus(D,j0,N)): return False
    eD = Fs(D); numD, denD = eD.numerator(), eD.denominator()
    ddeg = {'Cj': 2*denD.degree(u), 'Cn': denD.degree(w), 'K': denD.degree(qs)}
    k1 = {'Cj': 2*bc0[0], 'Cn': bc0[1], 'K': k0+1}          # affine value of k+1
    for (eq,eu,ew) in numD.dict():        # q-degree of each monomial <= k+1
        coef = {'Cj': k1['Cj']+ddeg['Cj']-2*eu, 'Cn': k1['Cn']+ddeg['Cn']-ew,
                'K': k1['K']+ddeg['K']-eq}
        if not ge_on_cone(coef, 0, j0, N): return False
    return True

def step3AB(A,B,C,K,D):                   # A*, B* of Step 3
    a, bc0, k0 = split_K(K); qk = Fs(K)/Fs(a)
    A,B,C,D = [Fs(x) for x in (A,B,C,D)]
    AA = (-D^2*A/a + B*D*qk - C*a*qk^2) / (qk^2 * qs^2)
    BB = 2*A*D/(a*qk) - B
    return AA, BB

def image_ok(tpl, j0, N):                 # (iii): Step-3 image polynomial, B*(0)=1
    AA, BB = step3AB(*tpl)
    return qm1_ok(AA) and qm1_ok(BB) and order_ge(AA,0,j0,N) and is_one_plus(BB,j0,N)

def least(test, j0, lo=-4):
    for N in range(lo, 13):
        if test(j0, N): return N
    return None

def certify(tpl, j0):
    """least N for (i), (ii), (iii) separately, and for all three (= the cone)."""
    A,B,C,K,D = tpl
    Ni   = least(lambda j0,N: cond26(A,B,C,j0,N), j0)
    Nii  = least(lambda j0,N: kD_ok(K,D,j0,N), j0)
    Niii = least(lambda j0,N: image_ok(tpl,j0,N), j0)
    if None in (Ni,Nii,Niii): return Ni,Nii,Niii,None
    return Ni, Nii, Niii, max(Ni,Nii,Niii)

# ======================================================================
#  Walk the pass-tables in the order of the sequence, with their case conditions.
#  Coverage: the least d=n-2j at which a generic tuple is used is a constant
#  read off from the pass boundary (B_p = 9n/2 + const); a j-free tuple
#  (special row j=0, bridge) is used for every n>=4.
# ======================================================================
def dmin_even(off, r):  return -2*((off-1-r)//9)
def dmin_odd (base, r): return 1 - 2*((base-r)//9)
def gen(dic, r, cond, j0, dm): return ('gen', dic, r, cond, j0, dm)
def spc(dic, r, cond):         return ('spc', dic, r, cond, 0, 4)

E1 = sum([[spc(s1,r,"j=0"), gen(gp1,r,"j>=1",1,dmin_even(-7,r))] for r in range(1,7)],[]) \
   + [gen(gp1,r,"j>=0",0,dmin_even(-7,r)) for r in (7,8,9)]
E2 = sum([[spc(s2,r,"c%d"%r), gen(gp2,r,"j>=1",1,dmin_even(-8,r))] for r in range(1,6)],[]) \
   + [gen(gp2,r,"j>=0",0,dmin_even(-8,r)) for r in range(6,10)]
O1 = sum([[spc(s1,r,"j=0"), gen(gp1,r,"j>=1",1,dmin_odd(-4,r))] for r in range(1,7)],[]) \
   + [gen(gp1,r,"j>=0",0,dmin_odd(-4,r)) for r in (7,8,9)]
O2 = sum([[spc(o2,r,"d%d"%r), gen(go2,r,"j>=1",1,dmin_odd(-7,r))] for r in range(1,4)],[]) \
   + [gen(go2,r,"j>=0",0,dmin_odd(-7,r)) for r in range(4,10)]
BR = [spc(br,r,"b%d"%r) for r in range(1,9)]

WALK = [("Pass 1, even n", E1),
        ("Bridge 2 (c1..c5) + Pass 2, even n", E2),
        ("Pass 1, odd n  (same formulas, odd boundary)", O1),
        ("Bridge 3 (d1..d3) + Pass 2 (rows at half-integer j), odd n\n    (pass 2 is walked by the integer index m=9j+r of go2, m+5/2 = paper index;\n     j and n-2j in the cones refer to this integer index)", O2),
        ("Bridge 1 (b1..b8, both parities, j-free)", BR)]

print("PASS-TABLE-ORDERED VERIFICATION of Steps 1 & 2 by the polynomiality criterion")
print("  (i) triple satisfies (3.4)   (ii) (3.5): k>=0, D(0)=1, deg D<=k+1   (iii) Step-3 image satisfies (3.4)")
print("  cones: generic {j>=j0, n-2j>=N};  j-free tuples {n>=N}.  Uniform in (n,j).")
FAIL = []
for pname, walk in WALK:
    print("\n"+"="*74+"\n=== %s   (%d tuples) ===\n"%(pname, len(walk))+"="*74)
    for kind, dic, r, cond, j0, dm in walk:
        tpl = dic[r]
        a, bc0, k0 = split_K(tpl[3])
        Ni, Nii, Niii, N = certify(tpl, j0)
        lab = ("m=9j+%d"%r) if kind=='gen' else ("%-7s"%cond if cond[0] in "bcd" else "m=%d (j=0)"%r)
        if kind=='gen': lab += " [%s]"%cond
        if dic is go2:   # odd pass-2 index m -> row of Appendix E at half-integer j
            lab += "  = App. E row %d at j%s1/2" % ((r-2, "+") if r >= 3 else (r+7, "-"))
        if N is None:
            FAIL.append((pname,lab)); print("  %-16s *** NOT PROVED (%s,%s,%s)"%(lab,Ni,Nii,Niii)); continue
        ok = N <= dm
        if not ok: FAIL.append((pname,lab,"coverage"))
        Ks = "%s*q^{%s}"%(a, kstr(k0,bc0))
        if kind=='gen':
            print("  %-16s K=%-16s D=%s"%(lab, Ks, pp(tpl[4])))
            print("  %-16s (i) n-2j>=%d  (ii) n-2j>=%d  (iii) n-2j>=%d  => cone {j>=%s, n-2j>=%d};"
                  " used down to n-2j=%d: %s"%("", max(Ni,0), max(Nii,0), max(Niii,0), j0, max(N,0), dm,
                                              "OK" if ok else "*** COVERAGE GAP"))
        else:
            print("  %-16s K=%-16s D=%s"%(lab, Ks, pp(tpl[4])))
            print("  %-16s (i) n>=%d  (ii) n>=%d  (iii) n>=%d  => cone {n>=%d}; used for n>=4: %s"
                  %("", max(Ni,0), max(Nii,0), max(Niii,0), max(N,0), "OK" if ok else "*** COVERAGE GAP"))

# ======================================================================
#  POLYNOMIALITY RANGES printed in the tables, and the three EXITS.
# ======================================================================
print("\n"+"="*74+"\n=== POLYNOMIALITY RANGES of the generic rows (floored at n-2j>=0) ===\n"+"="*74)
P1 = (0,1,3,2,0,0,4,3,1); P2 = (0,3,2,0,0,2,4,3,1)
for name, fam, j0of, tab in (("pass 1, row", gp1, lambda r: 1 if r<=6 else 0, P1),
                             ("pass 2, row", gp2, lambda r: 1 if r==1 else (1/2 if r<=5 else 0), P2)):
    for r in range(1,10):
        A,B,C = fam[r][:3]; j0 = j0of(r)
        p = max(least(lambda j0,N: cond26(A,B,C,j0,N), j0), 0)
        ok = (p == tab[r-1])
        if not ok: FAIL.append((name,r,"range"))
        print("  %s %d : (3.4) holds on {j>=%s, n-2j>=%d}   %s"%(name, r, j0, p, "OK" if ok else "*** MISMATCH"))

def single_order(X):
    bl = blocks(X); assert len(bl)==1
    (bc,P), = bl.items(); c = affine(bc,qval(P))
    assert c['Cj'] + 2*c['Cn'] == 0           # order depends on d=n-2j only
    return c['K'], c['Cn']                    # order = K + Cn*d
print("\n=== EXITS (where a pass ends, Remark 3.4): the successor row does not satisfy (3.4) (A has a negative power of q) ===")
for lab, X, d in (("pass 1, n even: row 3 at n-2j=2", gp1[3][0], 2),
                  ("pass 1, n odd : row 7 at n-2j=3", gp1[7][0], 3),
                  ("pass 2        : row 2 at n-2j=2", gp2[2][0], 2)):
    K0, cn = single_order(X); o = K0 + cn*d
    print("  %s :  A = %s, one block of q-order %s = %d < 0 : %s"
          % (lab, pp(Fs(X)), kstr(K0,(0,cn)).replace("n","(n-2j)"), o, o<0))
    if o >= 0: FAIL.append(lab)

print("\n"+"#"*74)
if FAIL:
    print("RESULT: *** FAILURE ***  %s"%FAIL); sys.exit(1)
print("RESULT: STEPS 1 & 2 PROVED UNIFORMLY for ALL (n,j).")
print("  Every pass-table tuple, walked in the order of the sequence with its case")
print("  condition: its triple and its Step-3 image satisfy (3.4) and it satisfies (3.5)")
print("  on a cone containing every place where the sequence uses the tuple, so by")
print("  the polynomiality criterion its (k,a,D) are those of NextABC.  The")
print("  polynomiality ranges of the tables and the three exits are certified too.")
print("#"*74)
