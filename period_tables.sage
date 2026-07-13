# Generate the exact signed Hankel-determinant period tables Delta_N^{(n+2)}
# for n = 2 and n = 3, straight from the H-fraction data (no guessing).
#
# Method:  iterate NextABC to get the periodic data (k_j, v_j) with
#   k_j = val A^{(j+1)},   v_j = -a^{(j+1)}   (partial numerators),
# then apply eq:(detformula):
#   s_0 = 0,  s_j = k_0+...+k_{j-1} + j,
#   Delta_{s_j} = (-1)^{eps_j} * prod_{i<j} v_i^{s_j - s_i},
#   eps_j = sum_{i<j} binomial(k_i+1, 2).
# Every other Delta_N is 0.  We print Delta_N for N over one (anti)period,
# each factored as  sign * 2^E  to expose the sign pattern.
load('nextabc.sage')

def periodic_data(n, maxlen=80):
    """Return callables kf(j), vf(j) for the H-fraction data, plus (pre, per)."""
    from verify_base import init_tuple  # not a module; inline instead below
    raise RuntimeError

# --- inline the orbit computation (verify_base.sage is a script, not importable) ---
Qp = q^2 - q + 1
def init_tuple(n):
    if n == 1:
        A, B, C = R(-1), R(1 - q - q^2), R(q)
        for f0 in [1, 0, 1]:
            A, B, C = R((A + f0*B + f0^2*C)/q), R(B + 2*f0*C), R(q*C)
        return A, B, C
    return R(-q^(n-2)), R(-((q^2 - 3*q + 1)*q^n + Qp)/(q-1)), R(q^(n+3))

def orbit(n, maxlen=80):
    seq = [init_tuple(n)]
    kaD = []
    for _ in range(maxlen):
        A, B, C = seq[-1]
        As, Bs, Cs, k, a, D = nextABC(A, B, C)
        kaD.append((k, a, D))
        if (As, Bs, Cs) in seq:
            pre = seq.index((As, Bs, Cs))
            return kaD, pre, len(seq) - pre
        seq.append((As, Bs, Cs))
    raise RuntimeError("no period for n=%d" % n)

def data(n):
    """kf(j), vf(j) for all j>=0 (periodic after pre-period)."""
    kaD, pre, per = orbit(n)
    def idx(j):
        return j if j < pre else pre + ((j - pre) % per)
    kf = lambda j: kaD[idx(j)][0]
    vf = lambda j: -kaD[idx(j)][1]      # v_j = -a^{(j+1)}
    return kf, vf, pre, per

def factor2(v):
    """Return (sign, E) with v = sign * 2^E, for v in {+-1,+-2,...}."""
    v = QQ(v)
    s = 1 if v > 0 else -1
    return s, ZZ(abs(v)).valuation(2)

def fmt(d):
    if d == 0: return "  0 "
    s, E = factor2(d)
    core = ("+" if s > 0 else "-") + ("2" if E == 1 else "1")
    return "%3d " % d

def table(n, Nmax):
    kf, vf, pre, per = data(n)
    P = 2*n*(n+1)
    # surviving indices s_j and their determinants, far enough to cover Nmax
    surv = {}
    s = 0; j = 0
    # s_0 = 0 -> Delta_0 = 1 (empty product), eps_0 = 0
    while s <= Nmax:
        # Delta_{s_j}
        eps = sum(binomial(kf(i)+1, 2) for i in range(j))
        prod = QQ(1)
        for i in range(j):
            prod *= QQ(vf(i))^(s - (sum(kf(t) for t in range(i)) + i if i >= 1 else 0))
        Delta = (-1)^eps * prod
        surv[s] = Delta
        # advance to s_{j+1}
        s = s + kf(j) + 1
        j += 1
    print("=== n = %d :  (anti)period P = 2n(n+1) = %d,  orbit period = %d ===" % (n, P, per))
    print("  N   :  Delta_N     (sign*2^E)   |   nonzero only at surviving indices")
    for N in range(Nmax+1):
        d = surv.get(N, 0)
        if d == 0:
            tag = ""
        else:
            sg, E = factor2(d)
            tag = "  =  %s2^%d" % ("+" if sg > 0 else "-", E)
        marker = " <-" if d != 0 else ""
        print("  %3d :  %4d%s%s" % (N, d, tag, marker))
    # list just the nonzero subsequence for a compact view
    nz = [surv[N] for N in range(Nmax+1) if surv.get(N, 0) != 0]
    print("  nonzero subsequence:", nz)
    print()
    return surv, P

for n in [2, 3]:
    Nmax = 4*n*(n+1) - 1 if n == 3 else 2*n*(n+1) - 1   # two periods for odd n
    surv, P = table(n, Nmax)
    if n == 3:
        # check antiperiodicity Delta_{N+P} = -Delta_N
        bad = [N for N in range(P) if surv.get(N,0) != -surv.get(N+P,0)]
        print("  antiperiodicity Delta_{N+%d} = -Delta_N over N<%d : %s\n"
              % (P, P, "OK" if not bad else "FAILS at %s" % bad))
