# ============================================================================
#  certify_step3.sage  --  verbose, pass-table-ordered verification of STEP 3.
#
#  Step 3 of Algorithm N maps a tuple (A,B,C; k,a,D) to the successor triple
#  (A',B',C') via eq (AA/BB/CC).  Unlike Steps 1&2 this is a RATIONAL-FUNCTION
#  IDENTITY in q (with u=q^{2j}, w=q^n free): it needs no ordering of exponents,
#  so a single symbolic check settles it for ALL n,j at once.
#
#  For every tuple of the pass-tables we (i) compute (A',B',C'), (ii) verify the
#  identity symbolically, and (iii) say WHICH tuple (A',B',C') is -- i.e. where
#  the orbit goes next.  The tuple data + step3() + shift_j1/at_u + the bridge
#  triples all come from passtables.sage.
# ============================================================================
import sys, os
_o=sys.stdout; sys.stdout=open(os.devnull,'w')
load('passtables.sage')     # step3, shift_j1, at_u, dicts gp1..,go2,s1,s2,e30,e31,o2,br,p1_m2,p2_bd ; Fs,qs,u,w
sys.stdout=_o

def pp(e):                                       # simplify_full, then readable q,q^{2j},q^n
    try:    e = SR(str(e)).simplify_full()
    except Exception: pass
    s = str(e).replace('qs','Q_')
    for kk in (3,2):
        s = s.replace('u^%d'%kk, 'q^{%dj}'%(2*kk)).replace('w^%d'%kk, 'q^{%dn}'%kk)
    s = s.replace('u','q^{2j}').replace('w','q^n').replace('Q_','q')
    return s

FAIL=[]
def dstm(dr, mode):
    return {'same':"m=9j+%d"%dr, 'jshift':"m=9(j+1)+%d"%dr,
            'u1':"m=%d (j=0)"%dr, 'uq2':"m=%d (j=1)"%(9+dr)}[mode]

def T(src_dic, r, cond, passlab, dst_dic, dr, dcond, dstpass, mode='same'):
    A,B,C,K,D = [Fs(x) for x in src_dic[r]]
    AA,BB,CC = step3(A,B,C,K,D)
    d = dst_dic[dr]
    if   mode=='jshift': tgt=[Fs(x).subs({u:qs^2*u}) for x in d[:3]]
    elif mode=='u1':     tgt=[Fs(x).subs({u:1})      for x in d[:3]]
    elif mode=='uq2':    tgt=[Fs(x).subs({u:qs^2})   for x in d[:3]]
    else:                tgt=[Fs(x) for x in d[:3]]
    ok = (AA==tgt[0] and BB==tgt[1] and CC==tgt[2])
    if not ok: FAIL.append((passlab,r,cond))
    print("."*72)
    print("m=9j+%-2d [%-14s]     (%s)"%(r, cond, passlab))
    print("   Step 3 computes (A',B',C'); the identity in q (all n,j) gives (A',B',C') = %s"%ok)
    print("      A' = %s"%pp(d[0]))
    print("      B' = %s"%pp(d[1]))
    print("      C' = %s"%pp(d[2]))
    print("   ==> (A',B',C')  is the next tuple:  %s ,  %s  [%s]"%(dstpass, dstm(dr,mode), dcond))

def junction(txt):
    print("-"*72); print("   >>> JUNCTION:  %s"%txt)

# ============================ EVEN n =========================================
print("#"*72); print("# STEP 3  --  EVEN n :  Pass1 -> Pass2 -> Pass3 -> (Pass4=Pass2)"); print("#"*72)

print("\n=== Even Pass 1 : generic interior (j notin {0}) ===")
for r in range(1,9): T(gp1,r,"j notin {0}","Even Pass 1", gp1,r+1,"j notin {0}","Even Pass 1")
T(gp1,9,"j notin {0}","Even Pass 1", gp1,1,"j notin {0}","Even Pass 1",'jshift')
print("\n=== Even Pass 1 : j=0 chain ===")
for r in range(1,6): T(s1,r,"j=0","Even Pass 1", s1,r+1,"j=0","Even Pass 1")
T(s1,6,"j=0","Even Pass 1", gp1,7,"all j","Even Pass 1",'u1')
junction("Even Pass 1 boundary tuple (m=B1) = Even Pass 2, m=1  (values, in junc.sage)")

print("\n=== Even Pass 2 : generic interior (j notin {0}) ===")
for r in range(1,9): T(gp2,r,"j notin {0}","Even Pass 2", gp2,r+1,"j notin {0}","Even Pass 2")
T(gp2,9,"j notin {0}","Even Pass 2", gp2,1,"j notin {0}","Even Pass 2",'jshift')
print("\n=== Even Pass 2 : j=0 chain ===")
for r in range(1,5): T(s2,r,"j=0","Even Pass 2", s2,r+1,"j=0","Even Pass 2")
T(s2,5,"j=0","Even Pass 2", gp2,6,"all j","Even Pass 2",'u1')
junction("Even Pass 2 boundary tuple (m=B2) = Even Pass 3, m=1  (values, in junc.sage)")

print("\n=== Even Pass 3 : generic interior (j notin {0}) ===")
for r in range(1,9): T(gp3,r,"j notin {0}","Even Pass 3", gp3,r+1,"j notin {0}","Even Pass 3")
T(gp3,9,"j notin {0}","Even Pass 3", gp3,1,"j notin {0,1}","Even Pass 3",'jshift')
print("\n=== Even Pass 3 : j=0 chain, then j=1 chain ===")
for r in range(1,9): T(e30,r,"j=0","Even Pass 3", e30,r+1,"j=0","Even Pass 3")
T(e30,9,"j=0","Even Pass 3", e31,1,"j=1","Even Pass 3",'same')
for r in range(1,4): T(e31,r,"j=1","Even Pass 3", e31,r+1,"j=1","Even Pass 3")
T(e31,4,"j=1","Even Pass 3", gp3,5,"j notin {0}","Even Pass 3",'uq2')
junction("Even Pass 3 boundary tuple (m=B3) = Even Pass 2, m=1  (closes cycle: Pass4=Pass2)")

# ============================ ODD n ==========================================
print("\n\n"+"#"*72); print("# STEP 3  --  ODD n :  Pass1(=Even Pass1) -> Pass2 -> Bridge -> Pass1"); print("#"*72)
print("\n(Odd Pass 1 uses the SAME formulas/transitions as Even Pass 1 above.)")

print("\n=== Odd Pass 2 : generic interior (j notin {0}) ===")
for r in range(1,9): T(go2,r,"j notin {0}","Odd Pass 2", go2,r+1,"j notin {0}","Odd Pass 2")
T(go2,9,"j notin {0}","Odd Pass 2", go2,1,"j notin {0}","Odd Pass 2",'jshift')
print("\n=== Odd Pass 2 : j=0 chain ===")
for r in range(1,3): T(o2,r,"j=0","Odd Pass 2", o2,r+1,"j=0","Odd Pass 2")
T(o2,3,"j=0","Odd Pass 2", go2,4,"all j","Odd Pass 2",'u1')
junction("Odd Pass 2 boundary feeds the 7-tuple bridge  (entry p2_bd -> bridge#1)")

print("\n=== Odd Bridge : 7 j-free tuples ===")
def Tbr(r, dst, dstlab):
    A,B,C,K,D = [Fs(x) for x in br[r]]
    AA,BB,CC = step3(A,B,C,K,D); tgt=[Fs(x) for x in dst[:3]]
    ok=(AA==tgt[0] and BB==tgt[1] and CC==tgt[2])
    if not ok: FAIL.append(("Odd Bridge",r))
    print("."*72); print("bridge #%d [j-free]     (Odd Bridge)"%r)
    print("   Step 3 computes (A',B',C'); the identity in q (all n) gives (A',B',C') = %s"%ok)
    print("      A' = %s"%pp(dst[0])); print("      B' = %s"%pp(dst[1])); print("      C' = %s"%pp(dst[2]))
    print("   ==> (A',B',C')  is:  %s"%dstlab)
for r in range(1,7): Tbr(r, br[r+1], "Odd Bridge ,  bridge #%d"%(r+1))
Tbr(7, p1_m2, "Odd Pass 1 ,  m=2  [j=0]   (re-enters; closes the odd cycle)")

print("\n"+"#"*72)
if FAIL:
    print("RESULT: *** FAILURE ***  %s"%FAIL); sys.exit(1)
print("RESULT: STEP 3 VERIFIED for EVERY pass-table transition, as a symbolic")
print("  identity in q (u=q^{2j}, w=q^n free) -- hence for ALL n,j at once.")
print("  Each tuple's successor (A',B',C') is named above, tracing the full orbit:")
print("  Even: P1 -> P2 -> P3 -> (P4=P2).   Odd: P1 -> P2 -> bridge -> P1.")
print("#"*72)
