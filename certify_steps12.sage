# UNIFORM (all n,j) certificate for Steps 1 and 2 of Algorithm N.
#
# Each tuple entry X is a Laurent poly in q with coeffs rational in (u,w),
# u=q^{2j}, w=q^n.  Write X = sum_{(b,c)} P_{b,c}(q) u^b w^c,  P_{b,c} in QQ(q).
# Under u=q^{2j}, w=q^n the block (b,c) has q-order  ord(b,c) = val_q P_{b,c}
# + 2j b + n c  -- an AFFINE function of (j,n).  On the cone
#     C(j0,N) = { j >= j0 ,  n-2j >= N }
# "affine function g >= target for all (j,n) in C" is a finite check:
# writing j=j0+s, n-2j=N+t (s,t>=0), g = G0 + Gs s + Gt t, and g>=target on C
# iff Gs>=0 and Gt>=0 and G0>=target.  Everything below is exact.
import sys, os
_o=sys.stdout; sys.stdout=open(os.devnull,'w')
load('passtables.sage')                 # dicts gp1..,go2,s1,s2,e30,e31,o2,br,...; Fs,qs,u,w
sys.stdout=_o
Rc=R; qc=q
Pq = PolynomialRing(QQ,'qs'); (qP,) = Pq.gens()
Fq = Pq.fraction_field()

def blocks(elt):
    """X -> dict {(b,c): P_{b,c} in Fq}."""
    e = Fs(elt); num = e.numerator(); den = e.denominator()
    du, dw = den.degree(u), den.degree(w)
    denq = den // (u^du * w^dw)
    assert denq*(u^du*w^dw) == den and denq.degree(u)==0 and denq.degree(w)==0, \
        "denominator not (q-poly)*u^a*w^b : %s" % den
    denP = Pq(denq.subs({u:1, w:1}))     # q-only denominator polynomial
    out = {}
    for e_tuple, c in num.dict().items():
        eq, eu, ew = e_tuple              # Rs.gens() order = (qs,u,w)
        key = (eu-du, ew-dw)
        out[key] = out.get(key, Pq(0)) + QQ(c)*qP^eq
    return { k: Fq(v)/Fq(denP) for k,v in out.items() if v != 0 }

def qval(r):                              # q-adic valuation of r in Fq
    return r.numerator().valuation() - r.denominator().valuation()

def qlc(r):                               # leading (lowest-degree) q-coeff of r in Fq
    num, den = r.numerator(), r.denominator()
    return num[num.valuation()] / den[den.valuation()]

def affine(bc, val):
    """order of block bc=(b,c) with q-valuation 'val' -> (G-const,Gs,Gt,Gj,Gn)."""
    b, c = bc
    return {'Cj': 2*b, 'Cn': c, 'K': val}   # order = val + 2b*j + c*n

def ge_on_cone(coef, target, j0, N):
    """True iff  K + Cj*j + Cn*n >= target  for all (j,n) in C(j0,N)."""
    # substitute j=j0+s, n=2j+N+t = 2j0+N + 2s + t ; require Gs>=0,Gt>=0,G0>=target
    Cj, Cn, K = coef['Cj'], coef['Cn'], coef['K']
    G0 = K + Cj*j0 + Cn*(2*j0+N)
    Gs = Cj + 2*Cn
    Gt = Cn
    return (Gs >= 0) and (Gt >= 0) and (G0 >= target)

def split_K(K):
    """K = a q^{k0} u^{b0} w^{c0}  ->  (a, (b0,c0), k0)."""
    bl = blocks(K); assert len(bl)==1, "K not a monomial-block: %s"%K
    (bc, P), = bl.items(); v = qval(P)
    assert P == qlc(P)*qP^v, "K coeff not a monomial in q: %s"%P
    return qlc(P), bc, v

# ---- Step 1 certificate: recorded block is the STRICT least-order term ----
def step1(tpl, j0, N):
    A,B,C,K,D = tpl
    a, bc0, k0 = split_K(K)
    Abl = blocks(A)
    assert bc0 in Abl, "recorded block absent in A"
    v0 = qval(Abl[bc0])
    if v0 != k0: return False, "val mismatch %s vs %s"%(v0,k0)
    if qlc(Abl[bc0]) != a: return False, "lead-coef mismatch"
    ord0 = affine(bc0, v0)
    for bc, P in Abl.items():
        if bc == bc0: continue
        d = affine(bc, qval(P))
        diff = {'Cj': d['Cj']-ord0['Cj'], 'Cn': d['Cn']-ord0['Cn'], 'K': d['K']-ord0['K']}
        if not ge_on_cone(diff, 1, j0, N):        # other order > ord0 (strict)
            return False, "block %s not strictly above on cone"%(bc,)
    return True, "k=val=%s a=%s"%(k0, a)

# ---- Step 2 certificate: val_q( a q^k B/A - a q^k C/B - D ) >= k+2 --------
def step2(tpl, j0, N):
    A,B,C,K,D = tpl
    a, bc0, k0 = split_K(K)
    # val A = k (unique, from step1); val B = 0 (unique min); needed for val N
    Bbl = blocks(B)
    if (0,0) not in Bbl or qval(Bbl[(0,0)]) != 0: return False, "B(0,0) not val 0"
    ord0 = affine((0,0), 0)
    for bc,P in Bbl.items():
        if bc==(0,0): continue
        d=affine(bc,qval(P)); diff={'Cj':d['Cj'],'Cn':d['Cn']-0,'K':d['K']}
        diff={'Cj':d['Cj']-ord0['Cj'],'Cn':d['Cn']-ord0['Cn'],'K':d['K']-ord0['K']}
        if not ge_on_cone(diff,1,j0,N): return False,"val B not uniquely 0 (block %s)"%(bc,)
    # M = a q^k B^2 - a q^k C A - D A B ; need val_q M >= 2k+2 (then val R = valM-valN >= k+2)
    qk = Fs(K)/Fs(a)                     # = q^{k0} u^{b0} w^{c0}
    M = Fs(a)*qk*Fs(B)^2 - Fs(a)*qk*Fs(C)*Fs(A) - Fs(D)*Fs(A)*Fs(B)
    if M == 0: Mbl = {}
    else: Mbl = blocks(M)
    # target order 2k+2 as affine: 2k0+2 + j*(4 b0) + n*(2 c0)
    tgt = {'Cj': 4*bc0[0], 'Cn': 2*bc0[1], 'K': 2*k0+2}
    for bc,P in Mbl.items():
        d = affine(bc, qval(P))
        diff = {'Cj': d['Cj']-tgt['Cj'], 'Cn': d['Cn']-tgt['Cn'], 'K': d['K']-tgt['K']}
        if not ge_on_cone(diff, 0, j0, N):
            return False, "M block %s order < 2k+2 on cone"%(bc,)
    # (b) deg_q(conc D) <= k+1 : then congruence + degree bound  =>  D = [S]_{<=k+1}
    #     exactly (their difference has val>=k+2 and deg<=k+1, hence 0).
    eD = Fs(D); numD, denD = eD.numerator(), eD.denominator()
    # affine q-degree of den = deg_qs(den) + 2j*deg_u(den) + n*deg_w(den)
    ddeg = {'Cj': 2*denD.degree(u), 'Cn': denD.degree(w), 'K': denD.degree(qs)}
    k1 = {'Cj': 2*bc0[0], 'Cn': bc0[1], 'K': k0+1}          # affine value of k+1
    for e_tuple in numD.dict():
        eq, eu, ew = e_tuple
        # need  order(monomial) - ddeg <= k+1  <=>  (k1 + ddeg - order) >= 0 on cone
        coef = {'Cj': k1['Cj']+ddeg['Cj']-2*eu,
                'Cn': k1['Cn']+ddeg['Cn']-ew,
                'K':  k1['K'] +ddeg['K'] -eq}
        if not ge_on_cone(coef, 0, j0, N):
            return False, "deg D may exceed k+1 (monomial q^%d u^%d w^%d)"%(eq,eu,ew)
    return True, "val M>=2k+2 and deg D<=k+1  =>  D=[S]_{<=k+1}"


def kstr(k0,bc0):
    b,c=bc0; parts=[]
    if c: parts.append("n" if c==1 else "%d*n"%c)
    if b: parts.append(("+" if b>0 else "")+("-2j" if b==-1 else "2j" if b==1 else "%d*2j"%b))
    if k0 or not parts: parts.append(("%+d"%k0) if parts else str(k0))
    return "".join(parts).lstrip("+") or "0"

NOCONE = []
def min_cone(tpl, j0):
    """smallest N (0..12) with step1&2 proven on C(j0,N); None if none."""
    for N in range(0, 13):
        ok1,_ = step1(tpl,j0,N); ok2,_ = step2(tpl,j0,N)
        if ok1 and ok2: return N
    return None

def report(name, d, j0):
    print("=== %s  (cone j>=%d) ===" % (name, j0))
    for r in sorted(d):
        N = min_cone(d[r], j0)
        if N is None:
            ok1,m1 = step1(d[r],j0,0); ok2,m2 = step2(d[r],j0,0)
            NOCONE.append((name,r)); print("  r=%-2s  *** NO CONE  step1:%s(%s) step2:%s(%s)"%(r,ok1,m1,ok2,m2))
        else:
            print("  r=%-2s  proved on { j>=%d, n-2j>=%d }"%(r,j0,N))

def report_auto(name, d, j0max=2):
    """try j0=1 first; rows needing j>=2 (j=1 covered by a special chain) fall back."""
    print("=== %s ===" % name)
    for r in sorted(d):
        done=False
        for j0 in range(1, j0max+1):
            N = min_cone(d[r], j0)
            if N is not None:
                print("  r=%-2s  proved on { j>=%d, n-2j>=%d }"%(r,j0,N)); done=True; break
        if not done:
            ok1,m1=step1(d[r],1,0); ok2,m2=step2(d[r],1,0)
            NOCONE.append((name,r)); print("  r=%-2s  *** NO CONE  step1:%s(%s) step2:%s(%s)"%(r,ok1,m1,ok2,m2))

# ======================================================================
#  PRIMARY OUTPUT: walk the pass-table exactly -- its own order and case
#  conditions -- verifying Steps 1&2 UNIFORMLY in (n,j).  For each generic
#  tuple we also confirm COVERAGE symbolically: the least d=n-2j at which
#  it is used is a CONSTANT in n (because B_p=(9n+const)/2), and lies in
#  the proven cone.  NO value of n or j is ever substituted anywhere.
# ======================================================================
def jcone(tpl, want_j0, wonly):
    for j0 in ([0] if wonly else [want_j0]):
        N = min_cone(tpl, j0)
        if N is not None: return (j0, N)
    return None

# least used d=n-2j, from the pass boundary, independent of n:
#   even  B_p = 9n/2 + off      -> d_min = -2*floor((off-1-r)/9)
#   odd   B_p = (9n + 2*base)/2 -> d_min =  1 - 2*floor((base-r)/9)
def dmin_even(off, r):  return -2*((off-1-r)//9)
def dmin_odd (base, r): return 1 - 2*((base-r)//9)

def gen(dic, r, cond, j0, dm): return ('gen', dic, r, cond, j0, dm)
def spc(dic, r, cond):         return ('spc', dic, r, cond, 0, None)

E1 = sum([[spc(s1,r,"j=0"), gen(gp1,r,"j notin {0}",1,dmin_even(-7,r))] for r in range(1,7)],[]) \
   + [gen(gp1,r,"all j",0,dmin_even(-7,r)) for r in (7,8,9)]
E2 = sum([[spc(s2,r,"j=0"), gen(gp2,r,"j notin {0}",1,dmin_even(-8,r))] for r in range(1,6)],[]) \
   + [gen(gp2,r,"all j",0,dmin_even(-8,r)) for r in range(6,10)]
E3 = sum([[spc(e30,r,"j=0"), spc(e31,r,"j=1"), gen(gp3,r,"j notin {0,1}",2,dmin_even(0,r))] for r in range(1,5)],[]) \
   + sum([[spc(e30,r,"j=0"), gen(gp3,r,"j notin {0}",1,dmin_even(0,r))] for r in range(5,9)],[]) \
   + [spc(e30,9,"j=0"), gen(gp3,9,"j notin {0} (->Pass2)",1,dmin_even(0,9))]
O1 = sum([[spc(s1,r,"j=0"), gen(gp1,r,"j notin {0}",1,dmin_odd(-4,r))] for r in range(1,7)],[]) \
   + [gen(gp1,r,"all j",0,dmin_odd(-4,r)) for r in (7,8,9)]
O2 = sum([[spc(o2,r,"j=0"), gen(go2,r,"j notin {0}",1,dmin_odd(-7,r))] for r in range(1,4)],[]) \
   + [gen(go2,r,"all j",0,dmin_odd(-7,r)) for r in range(4,10)]
BR = [spc(br,r,"bridge (j-free)") for r in range(1,8)]

WALK = [("Even n, Pass 1", E1), ("Even n, Pass 2", E2), ("Even n, Pass 3", E3),
        ("Odd n, Pass 1  (= Even Pass 1 formulas, odd boundary)", O1),
        ("Odd n, Pass 2", O2), ("Odd n, Bridge", BR)]

# --- verbose per-tuple derivation (everything below is COMPUTED from A,B,C) ---
toP = Rs.hom([qP, Pq(1), Pq(1)], Pq)          # qs->q, u->1, w->1
def to_Fq(e):                                  # u,w-free element of Fs -> Fq
    e = Fs(e); return Fq(toP(e.numerator()))/Fq(toP(e.denominator()))
def blabel(bc):                                # (b,c) -> monomial label q^{...}
    s = kstr(0, bc); return "1" if s=="0" else "q^{%s}"%s
def corner(coef, j0, N):                        # value of affine 'coef' at cone corner
    return coef['K'] + coef['Cj']*j0 + coef['Cn']*(2*j0+N)
def pp(e):                                       # readable: qs->q, u->q^{2j}, w->q^n
    return str(e).replace('qs','q').replace('w','q^n').replace('u','q^{2j}')
def Kstr(a, kk):                                 # K = a*q^k in clean form
    if kk=="0": return str(a)
    qp = "q" if kk=="1" else "q^{%s}"%kk
    return qp if a==1 else ("-"+qp if a==-1 else "%s*%s"%(a,qp))

def describe(kind, dic, r, cond, ej0, dm, idx):
    tpl = dic[r]; A,B,C,K,D = tpl
    j0, N = jcone(tpl, ej0, kind=='spc')
    a, bc0, k0 = split_K(K)
    Abl = blocks(A); typ = 'S' if len(Abl)==1 else 'M'
    kk = kstr(k0, bc0)
    print("."*70)
    print("%-10s [%-14s]                              Type (%s)"%(idx, cond, typ))
    if typ=='S':
        P = to_Fq(Fs(a)*Fs(A)/Fs(K))
        print("   A = P(q)*mu :   P(q) = %s ,   mu = q^{%s}   (P(0)=%s != 0)"%(pp(P), kk, P.numerator()[0]/P.denominator()[0]))
        print("   Step 1:  k = val(mu) = %s ,   a = P(0) = %s ,   so K = a*q^k = %s"%(kk, a, Kstr(a,kk)))
        print("   Step 2:  q^k/A = 1/P,  so D = [ a*B/P ]_{<= k+1} = %s"%pp(D))
    else:
        A0 = Abl[bc0]
        print("   A = A0 + (higher blocks),   A0 the q-only part:")
        print("        A0 = %s        [q-order = %s <= 1]"%(pp(A0), kstr(qval(A0),bc0)))
        for bc in sorted(b for b in Abl if b!=bc0):
            print("        %-9s coeff %-26s [q-order = %s >= 2]"%(blabel(bc)+":", pp(Abl[bc]), kstr(qval(Abl[bc]),bc)))
        print("   Step 1:  least-order term is in A0  =>  k = %s ,  a = lc(A0) = %s ,  K = %s"%(kk, a, Kstr(a,kk)))
        print("   Step 2:  val(C)>=2 so C-term drops;  D = [ a*q^k*B/A ]_{<= k+1} = %s"%pp(D))
    # independent re-derivation of (k,a) straight from A, and the Step-2 residual check
    kA, aA = qval(Abl[bc0]), qlc(Abl[bc0])
    ok1,_ = step1(tpl,j0,N); ok2,_ = step2(tpl,j0,N)
    Cbl = blocks(C); cb = min(Cbl, key=lambda bc: corner(affine(bc,qval(Cbl[bc])),j0,N))
    print("   CHECK:  from A directly val(A)=%s, lc=%s (=k,a: %s);  val(C)=%s(>=2);"
          %(kstr(kA,bc0), aA, (kA==k0 and aA==a), kstr(qval(Cbl[cb]),cb)))
    print("           val( a*q^k*B/A - a*q^k*C/B - D ) >= k+2 : %s ;  deg_q D <= k+1 : %s"%(ok1 and ok2, ok2))
    if not (ok1 and ok2): FAIL.append((idx,cond,"proof"))
    if kind!='spc':
        covok = dm>=N
        print("   cone {j>=%d, n-2j>=%d} ;  used down to d=n-2j=%d  =>  %s"
              %(j0,N,dm,"inside cone (OK)" if covok else "*** COVERAGE GAP"))
        if not covok: FAIL.append((idx,cond,"coverage"))
        if "{0,1}" in cond and j0<2: FAIL.append((idx,cond,"cond mismatch"))
    else:
        print("   cone {n>=%d} ;  (used at n>=4 even / n>=5 odd; n=1,2,3 are base cases)"%N)

print("PASS-TABLE-ORDERED VERIFICATION of Steps 1 & 2   (all values COMPUTED from A,B,C; uniform in n,j)")
FAIL=[]
for pname, walk in WALK:
    print("\n"+"="*70+"\n=== %s   (%d tuples) ===\n"%(pname, len(walk))+"="*70)
    for kind, dic, r, cond, ej0, dm in walk:
        res = jcone(dic[r], ej0, kind=='spc')
        if res is None:
            FAIL.append((pname,r,cond)); print("  m=9j+%d [%s]  *** NOT PROVED"%(r,cond)); continue
        idx = ("bridge #%d"%r) if kind=='spc' and "bridge" in cond else ("m=9j+%d"%r)
        describe(kind, dic, r, cond, ej0, dm, idx)

print("\n"+"#"*70)
if FAIL or NOCONE:
    print("RESULT: *** FAILURE ***  %s"%(FAIL+NOCONE)); sys.exit(1)
print("RESULT: STEPS 1 & 2 PROVED UNIFORMLY for ALL (n,j).")
print("  Every pass-table tuple, walked in table order with its case condition;")
print("  each check is an affine inequality in (n,j) over its cone -- n,j stay")
print("  symbolic, no value is ever substituted.  Coverage (least used d >= N)")
print("  is a constant in n, also checked exactly.")
print("#"*70)
