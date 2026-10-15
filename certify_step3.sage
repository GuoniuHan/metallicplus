# ============================================================================
#  certify_step3.sage  --  verbose, pass-table-ordered verification of STEP 3.
#
#  Step 3 of Algorithm N maps a tuple (A,B,C; k,a,D) to the successor triple
#  (A',B',C') via eqs. (14)-(16) of the paper.  Unlike Steps 1&2 this is an
#  IDENTITY in Q(q,u,w) (u=q^{2j}, w=q^n free), valid whatever the relative size
#  of the exponents, so a single symbolic check settles it for ALL n,j at once.
#
#  For every tuple of the pass-tables we (i) compute (A',B',C'), (ii) verify the
#  identity symbolically, and (iii) say WHICH tuple (A',B',C') is -- i.e. where
#  the orbit goes next.  The tuple data + step3() + shift_j1/at_u + the bridge
#  triples all come from passtables.sage.
#
#  The orbit has the same shape for both parities of n >= 4:
#      n even:  Pass 1 -> Bridge 2 (c1..c5) -> Pass 2 -> Bridge 1 (b1..b8) -> Pass 1 [m=2]
#      n odd :  Pass 1 -> Bridge 3 (d1..d3) -> Pass 2 -> Bridge 1 (b1..b8) -> Pass 1 [m=2]
#  Pass 1, the Pass-2 rows m=9j+r and the three bridges are the same for
#  even and odd n.  For odd n, pass 2 is read at half-integer j (in the program,
#  the tuple at index m is the pass-2 row at index m+5/2); the parity only
#  selects Bridge 2 or Bridge 3, i.e. how Pass 1 is left.
# ============================================================================
import sys, os
_o=sys.stdout; sys.stdout=open(os.devnull,'w')
load('passtables.sage')     # step3, shift_j1, at_u, dicts gp1,gp2,go2,s1,s2,o2,br,p1_m2 ; Fs,qs,u,w
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

def junction(txt, gen_row, uB, dst, dstlab):
    """The boundary tuple of a pass: Step 3 at m=B-1 is a generic transition
    (checked above for all u,w), so its (A,B,C) is the generic row r_B at
    u=u_B.  Prove symbolically (identity in q, w) that this equals the first
    tuple of the next pass; that tuple then carries its OWN (K,D)."""
    lhs = [Fs(x).subs({u: uB}) for x in gen_row[:3]]
    ok = all(lhs[i] == Fs(dst[i]) for i in range(3))
    if not ok: FAIL.append(("junction", txt))
    print("-"*72); print("   >>> JUNCTION:  %s"%txt)
    print("       generic row at u = q^{2j_B} = %s gives (A,B,C) = %s :  identity in q, q^n = %s"
          %(pp(uB), dstlab, ok))

# ============================ PASS 1 (both parities) ========================
print("#"*72); print("# STEP 3  --  PASS 1  (both parities)"); print("#"*72)
print("\n=== Pass 1 : generic interior (j notin {0}) ===")
for r in range(1,9): T(gp1,r,"j notin {0}","Pass 1", gp1,r+1,"j notin {0}","Pass 1")
T(gp1,9,"j notin {0}","Pass 1", gp1,1,"j notin {0}","Pass 1",'jshift')
print("\n=== Pass 1 : j=0 chain ===")
for r in range(1,6): T(s1,r,"j=0","Pass 1", s1,r+1,"j=0","Pass 1")
T(s1,6,"j=0","Pass 1", gp1,7,"all j","Pass 1",'u1')

# ===================== BRIDGES 2 AND 3: PASS 1 -> PASS 2 ===========================
print("\n\n"+"#"*72); print("# STEP 3  --  BRIDGE 2 (n even) / BRIDGE 3 (n odd):  Pass 1 -> Pass 2"); print("#"*72)
print("\n--- even n: pass 1 ends at n-2j=2 ---")
junction("Pass 1 boundary tuple (m=B1: r=2, j=n/2-1) = bridge 2, c1", gp1[2], w/qs^2, s2[1], "Bridge 2, c1")
print("\n=== Bridge 2: c1..c5 (j-free) ===")
for r in range(1,5): T(s2,r,"c%d"%r,"Bridge 2", s2,r+1,"c%d"%(r+1),"Bridge 2")
T(s2,5,"c5","Bridge 2", gp2,6,"j=0","Pass 2, row 6 at j=0 (first tuple)",'u1')
print("\n--- odd n: pass 1 ends at n-2j=3 ---")
junction("Pass 1 boundary tuple (m=B1: r=6, j=(n-3)/2) = bridge 3, d1", gp1[6], w/qs^3, o2[1], "Bridge 3, d1")
print("\n=== Bridge 3: d1..d3 (j-free) ===")
for r in range(1,3): T(o2,r,"d%d"%r,"Bridge 3", o2,r+1,"d%d"%(r+1),"Bridge 3")
T(o2,3,"d3","Bridge 3", go2,4,"j=1/2","Pass 2, row 2 at j=1/2 (first tuple)",'u1')

# ============================ PASS 2 (both parities) ========================
print("\n\n"+"#"*72); print("# STEP 3  --  PASS 2 rows m=9j+r  (both parities)"); print("#"*72)
print("\n=== pass-2 rows 1..9 (u=q^{2j} free) ===")
for r in range(1,9): T(gp2,r,"generic","Pass 2", gp2,r+1,"generic","Pass 2")
T(gp2,9,"generic","Pass 2", gp2,1,"generic","Pass 2",'jshift')
print("\n(Odd n reads these rows at index m+5/2, i.e. u -> q^{+-1}u; Step 3 does not")
print(" involve u, so the transitions above give the odd ones.  Re-checked directly:)")
for r in range(1,9): T(go2,r,"odd, m+5/2","Pass 2 odd", go2,r+1,"odd, m+5/2","Pass 2 odd")
T(go2,9,"odd, m+5/2","Pass 2 odd", go2,1,"odd, m+5/2","Pass 2 odd",'jshift')
junction("Pass 2 boundary tuple (pass-2 row 1 at q^{2j}=q^{n-2}, both parities) = bridge 1, b1", gp2[1], w/qs^2, br[1], "Bridge 1, b1")

# ============================ BRIDGE 1 (both parities) ========================
print("\n\n"+"#"*72); print("# STEP 3  --  BRIDGE 1 (both parities):  b1..b8, j-free -> Pass1[m=2]"); print("#"*72)
print("\n(Identities in QQ(q,w), w=q^n: free of j and of the parity of n.)")
def Tbr(r, dst, dstlab):
    A,B,C,K,D = [Fs(x) for x in br[r]]
    AA,BB,CC = step3(A,B,C,K,D); tgt=[Fs(x) for x in dst[:3]]
    ok=(AA==tgt[0] and BB==tgt[1] and CC==tgt[2])
    if not ok: FAIL.append(("Bridge 1",r))
    print("."*72); print("b%d [j-free]     (Bridge 1)"%r)
    print("   Step 3 computes (A',B',C'); the identity in q (all n) gives (A',B',C') = %s"%ok)
    print("      A' = %s"%pp(dst[0])); print("      B' = %s"%pp(dst[1])); print("      C' = %s"%pp(dst[2]))
    print("   ==> (A',B',C')  is:  %s"%dstlab)
for r in range(1,8): Tbr(r, br[r+1], "Bridge 1 ,  b%d"%(r+1))
Tbr(8, p1_m2, "Pass 1 ,  m=2  [j=0]   (re-enters; closes the cycle, both parities)")

# bridge #8 vs the initial tuple: they differ only by the signs of A and C,
# so the orbit is periodic from m=2 on, with pre-period exactly 1.
okpre = (Fs(br[8][0]) == -Fs(s1[1][0]) and Fs(br[8][1]) == Fs(s1[1][1])
         and Fs(br[8][2]) == -Fs(s1[1][2]))
if not okpre: FAIL.append(("pre-period",))
print("-"*72)
print("   >>> b8 = (-A1, B1, -C1), A1,B1,C1 the initial tuple (Pass 1, m=1) : %s"%okpre)
print("       hence b8 != initial tuple: pre-period exactly 1.")

print("\n"+"#"*72)
if FAIL:
    print("RESULT: *** FAILURE ***  %s"%FAIL); sys.exit(1)
print("RESULT: STEP 3 VERIFIED for EVERY pass-table transition, and every pass")
print("  junction, as a symbolic identity in q (u=q^{2j}, w=q^n free) -- hence")
print("  for ALL n,j at once.")
print("  Each tuple's successor (A',B',C') is named above, tracing the full orbit:")
print("  n even: P1 -> Bridge 2 -> P2 -> Bridge 1 -> P1[m=2]")
print("  n odd : P1 -> Bridge 3 -> P2 -> Bridge 1 -> P1[m=2]   (pre-period 1).")
print("#"*72)
