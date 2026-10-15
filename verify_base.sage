# Base cases n = 1, 2, 3.
#
# These are NOT guessed: Algorithm N works verbatim at a numerical n, so we just
# start from the initial triple (A0,B0,C0) and iterate NextABC until the orbit
# repeats.  The script prints the whole orbit -- exactly the tuples displayed in
# Appendices A-C -- and checks the structural invariants used in Proposition 10
# and Section 4.3: pre-period 1; period 2, 9, 14; the last tuple of the
# period is (-A1, B1, -C1); sum over one period of (k+1) = 2n(n+1); and the two
# sign facts (I) prod_{i<P} v_i = -1, (II) X(n) = eps_P + sum_{v_i<0} s_i = n
# mod 2 (so Delta_{2n(n+1)} = (-1)^n), with v_i = -a^{(i+1)}.
load('nextabc.sage')
Qp = q^2 - q + 1

def init_tuple(n):
    """The m=1 tuple (A0,B0,C0)."""
    if n == 1:
        # derived by 3 cut-lemma steps from  q*Phi^2 + ((1+q)(1-q)-q)*Phi - 1 = 0,
        # with Phi^{(l)}(0) = 1,0,1  (l=0,1,2); this reproduces Remark rem:n1.
        A, B, C = R(-1), R(1 - q - q^2), R(q)
        for f0 in [1, 0, 1]:
            A, B, C = R((A + f0*B + f0^2*C)/q), R(B + 2*f0*C), R(q*C)
        return A, B, C
    # n >= 2 : the initial triple of Proposition (prop:init)
    return R(-q^(n-2)), R(-((q^2 - 3*q + 1)*q^n + Qp)/(q-1)), R(q^(n+3))

def orbit(n, maxlen=80):
    """Iterate NextABC from the initial triple; return the tuples until repeat."""
    seq = [init_tuple(n)]        # seq[i] = (A,B,C) at step m=i+1
    kaD = []                     # kaD[i] = (k,a,D) produced FROM seq[i]
    for _ in range(maxlen):
        A, B, C = seq[-1]
        assert A != 0 and C != 0 and B(0) == 1 and C(0) == 0, "invalid tuple, n=%d" % n
        As, Bs, Cs, k, a, D = nextABC(A, B, C)
        kaD.append((k, a, D))
        if (As, Bs, Cs) in seq:
            pre = seq.index((As, Bs, Cs))
            return seq, kaD, pre, len(seq) - pre
        seq.append((As, Bs, Cs))
    raise RuntimeError("no period found for n=%d within %d steps" % (n, maxlen))

allok = True
for n in [1, 2, 3]:
    seq, kaD, pre, per = orbit(n)
    print("=== n = %d :  pre-period %d, period %d ===" % (n, pre, per))
    for i in range(len(seq)):
        A, B, C = seq[i]; k, a, D = kaD[i]
        print("  m=%-2d  A=%s ; B=%s ; C=%s ; K=%s ; D=%s"
              % (i+1, A, B, C, a*q^k, D))
    ks = [kaD[i][0] for i in range(pre, pre + per)]          # one full period
    S = sum(k + 1 for k in ks)
    A1, B1, C1 = seq[0]
    last = (seq[per] == (-A1, B1, -C1))                       # tuple m = 1+P
    # sign facts over i = 0..P-1, i.e. m = 1..P
    prodv = prod(-kaD[i][1] for i in range(per))
    s_i = 0; X = 0
    for i in range(per):
        k, a = kaD[i][0], kaD[i][1]
        if -a < 0: X += s_i
        X += k*(k+1)//2; s_i += k + 1
    ok = (pre == 1) and (per == {1:2, 2:9, 3:14}[n]) and last and (S == 2*n*(n+1)) \
         and (prodv == -1) and ((X - n) % 2 == 0)
    allok &= ok
    print("  invariants: pre-period=%d (exp 1); period=%d (exp %d); tuple m=1+P = (-A1,B1,-C1): %s;"
          % (pre, per, {1:2, 2:9, 3:14}[n], last))
    print("              sum_{period}(k+1)=%d (exp 2n(n+1)=%d); prod_{i<P} v_i=%s (exp -1); X(n)=%d = n mod 2: %s  :  %s\n"
          % (S, 2*n*(n+1), prodv, X, (X-n) % 2 == 0, "OK" if ok else "*** FAIL"))

print("BASE CASES n=1,2,3 (computed from the initial triple):",
      "ALL OK" if allok else "FAILURES ABOVE")
