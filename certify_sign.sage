# UNIFORM (all n >= 4) certificate for the sign of the (anti)periodicity
# (Lemma 15 of the paper, Section 4.3) and for  sum (k_i+1) = 2n(n+1)  over one
# period (the hypothesis s_P = L of Lemma 14).
#
# Over one period, m = 1..P (P = 9n-10 for n even, 9n-13 for n odd), the
# orbit of Section 3.5 is a list of SEGMENTS: single j-free tuples (special
# rows j=0, bridges) and runs of FULL blocks j = lo..hi of a pass.  For each
# tuple, K = a q^k with a a constant and k = k0 + 2*b0*j + c0*n read off the
# values of K (b0,c0 = exponents of u=q^{2j}, w=q^n).  With n = 2t (even) or
# n = 2t+1 (odd) and t symbolic, every quantity below is a sum of polynomials
# in (t, j) over ranges with polynomial end points, computed EXACTLY by
# symbolic summation:
#     L     = sum (k^{(m)}+1)                      (must be 2n(n+1))
#     POS   = #{m : a^{(m)} > 0}                   (must be odd)
#     SE    = sum nu_2(a^{(m)})  (2-adic valuation)    (must be 0)
#     X     = eps_P + sum_{m: a^{(m)}>0} s_{m-1},  eps_P = sum binom(k^{(m)}+1, 2),
#             s_i = sum_{m <= i} (k^{(m)}+1)        (X - n must be even)
# where i = m-1 (so v_i = -a^{(m)} < 0  iff  a^{(m)} > 0).  Parity of a
# polynomial f(t) is decided by the integer-valued criterion: (f(t)-c)/2 is
# integer-valued on Z iff it takes integer values at deg+1 consecutive
# integers (Newton's forward differences).  No value of n is substituted.
import sys, os
_o=sys.stdout; sys.stdout=open(os.devnull,'w')
load('passtables.sage')        # gp1, gp2, go2, s1, s2, o2, br ; Fs, qs, u, w
sys.stdout=_o

Pq = PolynomialRing(QQ,'qs'); (qP,) = Pq.gens()
def split_K(K):
    """K = a q^{k0} u^{b0} w^{c0}  ->  (a, b0, c0, k0)."""
    e = Fs(K); num, den = e.numerator(), e.denominator()
    assert len(num.monomials())==1 and len(den.monomials())==1, "K not a monomial: %s"%K
    (eq,eu,ew), c = list(num.dict().items())[0]
    (fq,fu,fw), d = list(den.dict().items())[0]
    return QQ(c)/QQ(d), eu-fu, ew-fw, eq-fq

t, j = var('t j')
def v2(x):
    x = QQ(x); return x.numerator().valuation(2) - x.denominator().valuation(2)

def tup(T, jj):       # one tuple at block jj  ->  (a, k as expression)
    a, b0, c0, k0 = split_K(T[3])
    return a, k0 + 2*b0*jj + c0*NN
def segs(parity):
    """the orbit over one period m = 1..P, as a list of segments."""
    S = []
    single = lambda T, jj=0: S.append(('one', T, jj))
    block  = lambda fam, lo, hi: S.append(('blk', fam, lo, hi))
    for r in range(1,7): single(s1[r])                  # m = 1..6 (j=0)
    for r in (7,8,9):    single(gp1[r], 0)              # rows 7-9 at j=0
    if parity == 0:      # n = 2t
        block(gp1, 1, t-2)                              # full pass-1 blocks
        single(gp1[1], t-1)                             # last block: row 1
        for r in range(1,6): single(s2[r])              # c1..c5
        for r in (6,7,8,9): single(gp2[r], 0)           # pass 2, rows 6-9 at j=0
        block(gp2, 1, t-2)                              # full pass-2 blocks
    else:                # n = 2t+1
        block(gp1, 1, t-2)
        for r in range(1,6): single(gp1[r], t-1)        # last block: rows 1-5
        for r in range(1,4): single(o2[r])              # d1..d3
        for r in range(4,10): single(go2[r], 0)         # pass 2 from row 2 at j=1/2
        block(go2, 1, t-2)                              # full pass-2 blocks
        for r in (1,2): single(go2[r], t-1)             # rows 8,9 (generic index) of the last full block
    for r in range(1,8): single(br[r])                  # b1..b7  (b8 is m = P+1)
    return S

def integer_valued(f):
    """f in QQ[t] takes integer values on Z (Newton's forward differences)."""
    f = PolynomialRing(QQ,'T')(f)
    return all(f(x) in ZZ for x in range(f.degree()+1))

ALL = True
for parity in (0,1):
    NN = 2*t + parity
    s = 0; L = 0; POS = 0; SE = 0; EPS = 0; Y = 0; P = 0
    print("="*72); print("n = 2t%s  (t >= 2)"%("" if parity==0 else "+1")); print("="*72)
    for sg in segs(parity):
        if sg[0] == 'one':
            _, T, jj = sg
            a, k = tup(T, jj)
            if a > 0: Y += s; POS += 1
            EPS += k*(k+1)/2; SE += v2(a); s += k+1; L += k+1; P += 1
        else:
            _, fam, lo, hi = sg
            rows = [tup(fam[r], j) for r in range(1,10)]
            ln = sum(k+1 for (a,k) in rows).simplify_full()
            assert diff(ln, j) == 0, "block length depends on j: %s"%ln   # constant along the run
            nb = hi - lo + 1
            off = 0; Yb = 0; Eb = 0
            for (a,k) in rows:                 # inside block j: s = s + (j-lo)*ln + off
                if a > 0: Yb += s + (j-lo)*ln + off
                Eb += k*(k+1)/2; off += k+1
            Y   += sum(Yb, j, lo, hi)
            EPS += sum(Eb, j, lo, hi)
            POS += nb*sum(1 for (a,k) in rows if a > 0)
            SE  += nb*sum(v2(a) for (a,k) in rows)
            s += nb*ln; L += nb*ln; P += 9*nb
    L = L.simplify_full(); P = P.simplify_full()
    X = (EPS + Y).simplify_full(); POS = POS.simplify_full()
    Lok  = bool((L - 2*NN*(NN+1)).simplify_full() == 0)
    Pok  = bool((P - (9*NN - (10 if parity==0 else 13))).simplify_full() == 0)
    POSp = POS.polynomial(QQ); Xp = X.polynomial(QQ); NNp = NN.polynomial(QQ)
    posok = integer_valued((POSp - 1)/2)
    sgnok = integer_valued((Xp - NNp)/2)
    print("  number of tuples P            = %s   (= 9n-%d: %s)"%(P, 10 if parity==0 else 13, Pok))
    print("  sum (k+1)  = s_P              = %s   (= 2n(n+1): %s)"%(L.factor(), Lok))
    print("  sum nu_2(a)                   = %s"%SE)
    print("  #{a > 0}                      = %s   (odd for all t: %s)"%(POS, posok))
    print("  X = eps_P + sum_{a>0} s       = %s"%Xp)
    print("  (X - n)/2 integer-valued      : %s   => Delta_{2n(n+1)} = (-1)^n"%sgnok)
    ALL &= Lok and Pok and SE == 0 and posok and sgnok

print("\n" + "#"*72)
if not ALL:
    print("RESULT: *** FAILURE ***"); sys.exit(1)
print("RESULT: for ALL n >= 4:  s_P = 2n(n+1);  sum e = 0 and #{a>0} odd, so")
print("  prod_{i<P} v_i = -1;  X(n) = n mod 2, so Delta_{2n(n+1)} = (-1)^n.")
print("#"*72)
