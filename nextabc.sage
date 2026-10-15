# =====================================================================
#  Algorithm NextABC (delta = 2) of Han 2016, over QQ[q], for the paper
#  "Hankel determinants for the (n+2)-shifted q-metallic numbers".
#
#  NextABC works for a CONCRETE integer n: a tuple is instantiated at a
#  concrete (n, j) and the result is an element of QQ[q].  It is used only
#  to compute the base cases n = 1, 2, 3 (verify_base.sage).  The proof for
#  all n >= 4 is symbolic: certify_step3.sage, certify_steps12.sage,
#  certify_sign.sage.
#
#  load('nextabc.sage') from a driver, then use nextABC / Q / R / q.
# =====================================================================

R = PolynomialRing(QQ, 'q')
q = R.gen()
FF = R.fraction_field()

def Q():
    return q^2 - q + 1

def nextABC(A, B, C):
    """(A*, B*, C*, k, a, D) = NextABC(A,B,C), all exact over QQ[q]."""
    A = R(A); B = R(B); C = R(C)
    assert A != 0 and C != 0, "A or C is zero"
    assert B(0) == 1, "B(0) != 1 : %s" % B
    assert C(0) == 0, "C(0) != 0 : %s" % C
    k = A.valuation()
    a = A[k]
    maxdeg = max(A.degree(), B.degree(), C.degree(), 1)
    prec = 2 * maxdeg + k + 30
    PS = PowerSeriesRing(QQ, 'q', default_prec=prec)
    x = PS.gen()
    Aps = PS(A); Bps = PS(B); Cps = PS(C)
    expr = (a * x^k * Bps) / Aps - (a * x^k * Cps) / Bps
    D = R(sum(expr[i] * q^i for i in range(k + 2)))
    assert D(0) == 1, "D(0) != 1 : %s" % D
    assert D.degree() <= k + 1, "deg D > k+1"
    Astar = FF(-D^2 * A / a + B * D * q^k - C * a * q^(2*k)) / q^(2*k+2)
    Bstar = FF(2 * A * D) / (a * q^k) - B
    Cstar = FF(-A * q^2 / a)
    for X, nm in [(Astar,'A*'), (Bstar,'B*'), (Cstar,'C*')]:
        assert X.denominator() == 1, "%s not a polynomial: %s" % (nm, X)
    return (R(Astar), R(Bstar), R(Cstar), k, a, D)


def check_transition(src, dst, label=""):
    """src, dst are 5-tuples (A,B,C,K,D). Verify
       NextABC(src.A,src.B,src.C) == (dst.A,dst.B,dst.C ; k,a,D)
       with a*q^k == src.K and D == src.D.  Returns True/False."""
    A, B, C, K, D = [R(x) for x in src]
    An, Bn, Cn, Kn, Dn = [R(x) for x in dst]
    As, Bs, Cs, k, a, Do = nextABC(A, B, C)
    ok = True
    msgs = []
    if As != An: ok = False; msgs.append("A* mismatch\n   got %s\n   exp %s" % (As, An))
    if Bs != Bn: ok = False; msgs.append("B* mismatch\n   got %s\n   exp %s" % (Bs, Bn))
    if Cs != Cn: ok = False; msgs.append("C* mismatch\n   got %s\n   exp %s" % (Cs, Cn))
    if R(a*q^k) != K: ok = False; msgs.append("K mismatch got %s exp %s" % (a*q^k, K))
    if Do != D: ok = False; msgs.append("D mismatch got %s exp %s" % (Do, D))
    if not ok:
        print("  [FAIL] %s" % label)
        for m in msgs: print("     " + m)
    return ok
