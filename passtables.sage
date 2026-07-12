# Symbolic Step-3 checker (author's CheckQ2.sage method), metallic data.
# Variables: w = q^n, u = q^{2j}  (q^{4j}=u^2, q^{n-2j}=w/u, q^{2j+c}=u q^c, ...).
# Every tuple entry is a Laurent poly in q with coefficients rational in (u,w).
# Steps 1,2 (k,a,D) are supplied BY HAND (taken here from the draft's K,D);
# Step 3 (eqAA/eqBB/eqCC) is checked to hold IDENTICALLY  =>  all n,j at once.
# Each transition is ALSO cross-checked at one concrete (n,j) against the real
# NextABC (nextabc.sage), guarding the transcription.

load('nextabc.sage')                 # Rc = R (QQ[q]), gen q=qc, nextABC
Rc = R; qc = q
Rs = PolynomialRing(QQ, ['qs','u','w']); qs,u,w = Rs.gens(); Fs = Rs.fraction_field()
Qs = qs^2 - qs + 1

phi = Rs.hom([qc, Rc(1), Rc(1)], Rc)     # qs->q, u->1, w->1 (u,w gone after subs)
def conc(expr, nv, jv):
    """Specialise a symbolic entry to concrete (n,j) as an element of QQ[q]."""
    e = Fs(expr).subs({u: qs^(2*jv), w: qs^nv})
    num, den = phi(e.numerator()), phi(e.denominator())
    assert den.divides(num), "not a polynomial at n=%d,j=%d" % (nv,jv)
    return num // den

def split_K(K):
    K = Fs(K); a = K.subs({qs:1, u:1, w:1}); return a, K/a     # a, q^k

def step3(A,B,C,K,D):
    a, qk = split_K(K)
    AA = (-D^2*A/a + B*D*qk - C*a*qk^2) / (qk^2 * qs^2)
    BB = 2*A*D/(a*qk) - B
    CC = -A*qs^2/a
    return Fs(AA), Fs(BB), Fs(CC)

def check(src, dst, nv, jv, label):
    # dst is the symbolic successor already expressed in (u,w); evaluate it at
    # the SAME (nv,jv) as src (a j+1 wrap is baked into dst via u->q^2 u).
    A,B,C,K,D = [Fs(x) for x in src]
    A2,B2,C2,K2,D2 = [Fs(x) for x in dst]
    AA,BB,CC = step3(A,B,C,K,D)
    sym = (AA==A2 and BB==B2 and CC==C2)
    # concrete cross-check vs real NextABC
    sc = (conc(A,nv,jv), conc(B,nv,jv), conc(C,nv,jv))
    As,Bs,Cs,k,a,Dout = nextABC(*sc)
    con = ((As,Bs,Cs)==(conc(A2,nv,jv),conc(B2,nv,jv),conc(C2,nv,jv))
           and a*qc^k==conc(K,nv,jv) and Dout==conc(D,nv,jv))
    print("  %-26s symbolic Step3: %-5s   concrete NextABC: %-5s  %s"
          % (label, sym, con, "OK" if (sym and con) else "*** FAIL"))
    return sym and con

# ============================ EVEN PASS 1 (generic block) ================
# r = 1..9, generic j (>=1 for r<=6, all j for r=7,8,9).  Draft lines 383-507.
Q = Qs
gp1 = {}
gp1[1] = (-((Q*qs^2-4*Q*qs+4*Q)*u^2 + (Q*qs-2*Q)*u + ((Q*qs-2*Q)*u+qs)*w)/((qs^2-2*qs+1)*u),
          -(2*(Q*qs-2*Q)*u + Q*w + Q)/(qs-1),
          -Q*u,
          Fs(2), -1/2*qs+1)
gp1[2] = (((Q*qs^2-2*Q*qs)*u + Q*qs^3*u^2 + ((Q*qs^2-2*Q*qs)*u+qs^2-4*qs+4)*w)/(8*(qs^3-2*qs^2+qs)*u),
          ((Q*qs^3-2*Q*qs^2)*u^2 + (Q*qs^2-2*Q*qs+2*Q)*u + ((Q*qs^2-2*Q*qs+2*Q)*u+qs^2-2*qs)*w)/(2*(qs^2-2*qs+1)*u),
          ((Q*qs^4-4*Q*qs^3+4*Q*qs^2)*u^2 + (Q*qs^3-2*Q*qs^2)*u + (qs^3+(Q*qs^3-2*Q*qs^2)*u)*w)/(2*(qs^2-2*qs+1)*u),
          Fs(-1/4), -1/2*qs+1)
gp1[3] = (2*w/(u*qs^3),
          -(Q*u*qs + (Q*u*qs+2*qs-4)*w)/((qs^2-qs)*u),
          ((Q*qs^3-2*Q*qs^2)*u + Q*qs^4*u^2 + (qs^3+(Q*qs^3-2*Q*qs^2)*u-4*qs^2+4*qs)*w)/(2*(qs^2-2*qs+1)*u),
          2*w/(u*qs^3), -(Q*u*qs - w)/((qs^2-qs)*u))
gp1[4] = (((Q*qs^3-Q*qs^2)*u^2 + Q*u*qs - (Q*u*qs+qs-1)*w)/((qs^2-qs)*u),
          -(Q*u*qs - (Q*u*qs+2*qs-2)*w)/((qs^2-qs)*u),
          -w/(u*qs),
          Fs(-1), Fs(1))
gp1[5] = (Q*u/qs,
          -(2*(Q*qs^2-Q*qs)*u - Q*w + Q)/(qs-1),
          ((Q*qs^4-Q*qs^3)*u^2 + Q*u*qs^2 - (Q*u*qs^2+qs^2-qs)*w)/((qs-1)*u),
          u/qs, (u*qs-1)/(qs-1))
gp1[6] = (-(Q*qs^3*u^2 - Q*u*qs - (Q*u*qs-1)*w)/((qs^2-2*qs+1)*u),
          (2*Q*qs^2*u - Q*w - Q)/(qs-1),
          -Q*u*qs,
          qs, -qs+1)
gp1[7] = (w/(u*qs^4),
          -(Q*u*qs + (Q*u*qs-2)*w)/((qs^2-qs)*u),
          (Q*qs^5*u^2 - Q*qs^3*u - (Q*qs^3*u-qs^2)*w)/((qs^2-2*qs+1)*u),
          w/(u*qs^4), -(Q*qs^2*u - w)/((qs^3-qs^2)*u))
gp1[8] = (((Q*qs^5-Q*qs^4)*u^2 - Q*qs^2*u + (Q*qs^2*u-qs+1)*w)/((qs^3-qs^2)*u),
          -(Q*qs^2*u - (Q*qs^2*u-2*qs+2)*w)/((qs^3-qs^2)*u),
          -w/(u*qs^2),
          Fs(1), Fs(1))
gp1[9] = (-Q*u,
          (2*(Q*qs^3-Q*qs^2)*u + Q*w - Q)/(qs-1),
          -((Q*qs^5-Q*qs^4)*u^2 - Q*qs^2*u + (Q*qs^2*u-qs+1)*w)/((qs-1)*u),
          -u, (qs^2*u-1)/(qs-1))

def shift_j1(t):    # tuple at (r=1, j+1): substitute u -> q^2 u
    return tuple(Fs(x).subs({u: qs^2*u}) for x in t)

RESULTS = []
def run_generic(name, gp, N, J):
    print("=== %s (generic block, all j) ===" % name)
    ok = True
    for r in range(1, 9):
        ok &= check(gp[r], gp[r+1], N, J, "%s  r=%d -> r=%d" % (name, r, r+1))
    ok &= check(gp[9], shift_j1(gp[1]), N, J, "%s  r=9 -> r=1(j+1)" % name)
    print("  --> %s" % ("ALL OK" if ok else "FAILURES"))
    RESULTS.append((name, ok))
    return ok

run_generic("EVEN PASS 1", gp1, 12, 3)

# ============================ EVEN PASS 2 (generic block) ================
# Draft lines 553-668.
gp2 = {}
gp2[1] = ((Q*u*qs + (Q*u*qs-Q*qs)*w - qs^2*u^2)/((qs^2-2*qs+1)*u),
          -(Q*w + Q - 2*u*qs)/(qs-1),
          -u,
          qs, -qs+1)
gp2[2] = (Q*w/(u*qs^3),
          -(Q*u + (Q*u-2*Q)*w)/((qs-1)*u),
          -(Q*u*qs^3 - (Q*qs^3 - Q*u*qs^3)*w - u^2*qs^4)/((qs^2-2*qs+1)*u),
          w/(u*qs^3), -(u*qs - w)/((qs^2-qs)*u))
gp2[3] = (((qs^3-qs^2)*u^2 - Q*u*qs + (Q*u*qs - Q*qs + Q)*w)/((qs^2-qs)*u),
          -(Q*u*qs - (Q*u*qs - 2*Q*qs + 2*Q)*w)/((qs^2-qs)*u),
          -Q*w/(u*qs),
          Fs(1), Fs(1))
gp2[4] = (-u/qs,
          (2*(qs^2-qs)*u + Q*w - Q)/(qs-1),
          -((qs^4-qs^3)*u^2 - Q*u*qs^2 - (Q*qs^2 - Q*qs - Q*u*qs^2)*w)/((qs-1)*u),
          -u/qs, -(Q - u*qs)/(qs-1))
gp2[5] = (-((qs^3-4*qs^2+4*qs)*u^2 + (Q*qs-2*Q)*u + ((Q*qs-2*Q)*u+Q)*w)/((qs^2-2*qs+1)*u),
          -(2*(qs^2-2*qs)*u + Q*w + Q)/(qs-1),
          -u*qs,
          Fs(2), -1/2*qs+1)
gp2[6] = (((Q*qs^3-2*Q*qs^2)*u + (Q*qs^2+(Q*qs^3-2*Q*qs^2)*u-4*Q*qs+4*Q)*w + u^2*qs^5)/(8*(qs^4-2*qs^3+qs^2)*u),
          ((qs^4-2*qs^3)*u^2 + (Q*qs^2-2*Q*qs+2*Q)*u + ((Q*qs^2-2*Q*qs+2*Q)*u+Q*qs-2*Q)*w)/(2*(qs^2-2*qs+1)*u),
          ((qs^5-4*qs^4+4*qs^3)*u^2 + (Q*qs^3-2*Q*qs^2)*u + (Q*qs^2+(Q*qs^3-2*Q*qs^2)*u)*w)/(2*(qs^2-2*qs+1)*u),
          Fs(-1/4), -1/2*qs+1)
gp2[7] = (2*Q*w/(u*qs^4),
          -(Q*u*qs^2 + (2*Q*qs+Q*u*qs^2-4*Q)*w)/((qs^3-qs^2)*u),
          ((Q*qs^3-2*Q*qs^2)*u + (Q*qs^2+(Q*qs^3-2*Q*qs^2)*u-4*Q*qs+4*Q)*w + u^2*qs^5)/(2*(qs^2-2*qs+1)*u),
          2*w/(u*qs^4), -(u*qs^2 - w)/((qs^3-qs^2)*u))
gp2[8] = (((qs^5-qs^4)*u^2 + Q*u*qs^2 - (Q*u*qs^2+Q*qs-Q)*w)/((qs^3-qs^2)*u),
          -(Q*u*qs^2 - (2*Q*qs+Q*u*qs^2-2*Q)*w)/((qs^3-qs^2)*u),
          -Q*w/(u*qs^2),
          Fs(-1), Fs(1))
gp2[9] = (u,
          -(2*(qs^3-qs^2)*u - Q*w + Q)/(qs-1),
          ((qs^5-qs^4)*u^2 + Q*u*qs^2 - (Q*u*qs^2+Q*qs-Q)*w)/((qs-1)*u),
          u, -(Q - u*qs^2)/(qs-1))
run_generic("EVEN PASS 2", gp2, 12, 3)

# ============================ EVEN PASS 3 (generic block) ================
# Draft lines 723-901. Generic = j not in [0,1] for r=1..4, j not in [0] r=5..9.
gp3 = {}
gp3[1] = (2*w/(u*qs),
          -(Q*u + (Q*u+2*qs^2-4*qs)*w)/((qs-1)*u),
          ((Q*qs^3-2*Q*qs^2)*u + Q*u^2*qs^2 + (qs^5-4*qs^4+4*qs^3+(Q*qs^3-2*Q*qs^2)*u)*w)/(2*(qs^2-2*qs+1)*u),
          2*w/(u*qs), -(Q*u - w*qs)/((qs-1)*u))
gp3[2] = (((Q*qs-Q)*u^2 + Q*u*qs - (qs^3+Q*u*qs-qs^2)*w)/((qs^2-qs)*u),
          -(Q*u - (Q*u+2*qs^2-2*qs)*w)/((qs-1)*u),
          -w*qs/u,
          Fs(-1), Fs(1))
gp3[3] = (Q*u/qs^3,
          -(2*(Q*qs-Q)*u + Q*qs - Q*w*qs)/(qs^2-qs),
          ((Q*qs^2-Q*qs)*u^2 + Q*u*qs^2 - (qs^4-qs^3+Q*u*qs^2)*w)/((qs-1)*u),
          u/qs^3, (u-qs)/(qs^2-qs))
gp3[4] = (-(Q*u^2*qs - Q*u*qs - (Q*u*qs-qs^2)*w)/((qs^2-2*qs+1)*u),
          (2*Q*u - Q*w - Q)/(qs-1),
          -Q*u/qs,
          qs, -qs+1)
gp3[5] = (w/(u*qs^2),
          -(Q*u + (Q*u-2*qs)*w)/((qs-1)*u),
          (Q*u^2*qs^3 - Q*u*qs^3 + (qs^4-Q*u*qs^3)*w)/((qs^2-2*qs+1)*u),
          w/(u*qs^2), -(Q*u - w)/((qs-1)*u))
gp3[6] = (((Q*qs-Q)*u^2 - Q*u + (Q*u-qs+1)*w)/((qs-1)*u),
          -(Q*u - (Q*u-2*qs+2)*w)/((qs-1)*u),
          -w/u,
          Fs(1), Fs(1))
gp3[7] = (-Q*u/qs^2,
          (2*(qs^3-2*qs^2+2*qs-1)*u + Q*w - Q)/(qs-1),
          -((Q*qs^3-Q*qs^2)*u^2 - Q*u*qs^2 - (qs^3-Q*u*qs^2-qs^2)*w)/((qs-1)*u),
          -u/qs^2, (u-1)/(qs-1))
gp3[8] = (-((Q*qs^2-4*Q*qs+4*Q)*u^2 + (Q*qs-2*Q)*u + ((Q*qs-2*Q)*u+qs)*w)/((qs^2-2*qs+1)*u),
          -(2*(Q*qs-2*Q)*u + Q*w + Q)/(qs-1),
          -Q*u,
          Fs(2), -1/2*qs+1)
gp3[9] = (((Q*qs^2-2*Q*qs)*u + Q*u^2*qs^3 + ((Q*qs^2-2*Q*qs)*u+qs^2-4*qs+4)*w)/(8*(qs^3-2*qs^2+qs)*u),
          ((Q*qs^3-2*Q*qs^2)*u^2 + (Q*qs^2-2*Q*qs+2*Q)*u + ((Q*qs^2-2*Q*qs+2*Q)*u+qs^2-2*qs)*w)/(2*(qs^2-2*qs+1)*u),
          ((Q*qs^4-4*Q*qs^3+4*Q*qs^2)*u^2 + (Q*qs^3-2*Q*qs^2)*u + (qs^3+(Q*qs^3-2*Q*qs^2)*u)*w)/(2*(qs^2-2*qs+1)*u),
          Fs(-1/4), -1/2*qs+1)
run_generic("EVEN PASS 3", gp3, 14, 3)

# odd pass 1 formulas are IDENTICAL to even pass 1 (verified by diff) -> covered.

# ============================ ODD PASS 2 (generic block) =================
# Draft lines 1125-1222.
go2 = {}
go2[1] = (((qs^3-qs^2)*u^2 + Q*u*qs - (Q*u*qs+Q*qs-Q)*w)/((qs^2-qs)*u),
          -(Q*u*qs - (2*Q*qs+Q*u*qs-2*Q)*w)/((qs^2-qs)*u),
          -Q*w/(u*qs),
          Fs(-1), Fs(1))
go2[2] = (u/qs,
          -(2*(qs^2-qs)*u - Q*w + Q)/(qs-1),
          ((qs^4-qs^3)*u^2 + Q*u*qs^2 - (Q*qs^2+Q*u*qs^2-Q*qs)*w)/((qs-1)*u),
          u/qs, -(Q - u*qs)/(qs-1))
go2[3] = ((Q*u*qs + (Q*u*qs-Q)*w - u^2*qs^3)/((qs^2-2*qs+1)*u),
          -(Q*w + Q - 2*u*qs^2)/(qs-1),
          -u*qs,
          qs, -qs+1)
go2[4] = (Q*w/(u*qs^4),
          -(Q*u*qs + (Q*u*qs-2*Q)*w)/((qs^2-qs)*u),
          -(Q*u*qs^3 - (Q*qs^2 - Q*u*qs^3)*w - u^2*qs^5)/((qs^2-2*qs+1)*u),
          w/(u*qs^4), -(u*qs^2 - w)/((qs^3-qs^2)*u))
go2[5] = (((qs^5-qs^4)*u^2 - Q*u*qs^2 + (Q*u*qs^2-Q*qs+Q)*w)/((qs^3-qs^2)*u),
          -(Q*u*qs^2 - (Q*u*qs^2-2*Q*qs+2*Q)*w)/((qs^3-qs^2)*u),
          -Q*w/(u*qs^2),
          Fs(1), Fs(1))
go2[6] = (-u,
          (2*(qs^3-qs^2)*u + Q*w - Q)/(qs-1),
          -((qs^5-qs^4)*u^2 - Q*u*qs^2 + (Q*u*qs^2-Q*qs+Q)*w)/((qs-1)*u),
          -u, -(Q - u*qs^2)/(qs-1))
go2[7] = (-((qs^5-4*qs^4+4*qs^3)*u^2 + (Q*qs^2-2*Q*qs)*u + ((Q*qs^2-2*Q*qs)*u+Q)*w)/((qs^3-2*qs^2+qs)*u),
          -(2*(qs^3-2*qs^2)*u + Q*w + Q)/(qs-1),
          -u*qs^2,
          Fs(2), -1/2*qs+1)
go2[8] = (((Q*qs^4-2*Q*qs^3)*u + (Q*qs^2+(Q*qs^4-2*Q*qs^3)*u-4*Q*qs+4*Q)*w + u^2*qs^7)/(8*(qs^5-2*qs^4+qs^3)*u),
          ((qs^6-2*qs^5)*u^2 + (Q*qs^3-2*Q*qs^2+2*Q*qs)*u + ((Q*qs^3-2*Q*qs^2+2*Q*qs)*u+Q*qs-2*Q)*w)/(2*(qs^3-2*qs^2+qs)*u),
          ((qs^6-4*qs^5+4*qs^4)*u^2 + (Q*qs^3-2*Q*qs^2)*u + ((Q*qs^3-2*Q*qs^2)*u+Q*qs)*w)/(2*(qs^2-2*qs+1)*u),
          Fs(-1/4), -1/2*qs+1)
go2[9] = (2*Q*w/(u*qs^5),
          -(Q*u*qs^3 + (2*Q*qs+Q*u*qs^3-4*Q)*w)/((qs^4-qs^3)*u),
          ((Q*qs^4-2*Q*qs^3)*u + (Q*qs^2+(Q*qs^4-2*Q*qs^3)*u-4*Q*qs+4*Q)*w + u^2*qs^7)/(2*(qs^3-2*qs^2+qs)*u),
          2*w/(u*qs^5), -(u*qs^3 - w)/((qs^4-qs^3)*u))
run_generic("ODD PASS 2", go2, 13, 3)

# ============================ ODD BRIDGE (7 tuples, w-only) ==============
# From program/derive_bridge.sage (verified n=5..16).  j-free => no u.
br = {}
br[1] = ((qs^4-2*qs^3+3*qs^2-2*qs+1)/(qs-1) + ((-qs^3+qs^2-2*qs+1)/(qs^2-qs))*w,
         (-2*qs^5+2*qs^4-2*qs^3-qs^2+qs-1)/(qs-1) + ((2*qs^3-qs^2+3*qs-1)/(qs-1))*w,
         (qs^6+qs^3)/(qs-1) + ((-qs^4-qs^2)/(qs-1))*w,
         Fs(-1), qs+1)
br[2] = ((-1/qs^3)*w,
         (-qs^2+qs-1)/(qs-1) + ((qs^3-qs^2+3*qs-2)/(qs^2-qs))*w,
         (qs^6-2*qs^5+3*qs^4-2*qs^3+qs^2)/(qs-1) + ((-qs^4+qs^3-2*qs^2+qs)/(qs-1))*w,
         -w/qs^3, (-qs^2+qs-1)/(qs-1) + (1/(qs^2-qs))*w)
br[3] = ((-qs^3-qs^2+qs-2)/(qs-1) + ((-qs^3+2*qs^2-2*qs+4)/(qs^2-qs))*w,
         (-qs^2+qs-1)/(qs-1) + ((-qs^3+qs^2-3*qs+4)/(qs^2-qs))*w,
         (-1/qs)*w,
         Fs(2), -1/2*qs+1)
br[4] = ((1/8*qs^3-3/8*qs^2+3/8*qs-1/4)/(qs-1) + ((1/8*qs^2-1/4*qs+1/4)/(qs-1))*w,
         (1/2*qs^4-1/2*qs^3-1/2*qs^2+qs-1)/(qs-1) + ((1/2*qs^3-qs^2+2*qs-1)/(qs-1))*w,
         (1/2*qs^5+1/2*qs^4-1/2*qs^3+qs^2)/(qs-1) + ((1/2*qs^4-qs^3+qs^2-2*qs)/(qs-1))*w,
         Fs(1/4), 1/2*qs+1)
br[5] = ((2/qs^2)*w,
         (-qs^2+qs-1)/(qs-1) + ((qs^2-3*qs+3)/(qs-1))*w,
         (-1/2*qs^5+3/2*qs^4-3/2*qs^3+qs^2)/(qs-1) + ((-1/2*qs^4+qs^3-qs^2)/(qs-1))*w,
         2*w/qs^2, (-qs^2+qs-1)/(qs-1) + (1/(qs-1))*w)
br[6] = (qs*w,
         (-qs^2+qs-1)/(qs-1) + ((-qs^2+3*qs-1)/(qs-1))*w,
         -w,
         qs*w, (-qs^2+qs-1)/(qs-1) + ((-qs^2+3*qs-1)/(qs-1))*w)
br[7] = ((1/qs^2)*w,
         (-qs^2+qs-1)/(qs-1) + ((-qs^2+3*qs-1)/(qs-1))*w,
         -qs^3*w,
         w/qs^2, (-qs^2+qs-1)/(qs-1) + (1/(qs-1))*w)
# exit target: pass 1, m=2 (j=0)  [even p1 r=2 j=0; odd p1 identical]
p1_m2 = (((qs^2-2*qs+2)*w + Q*qs - 2*Q)/(qs-1),
         ((qs^2-3*qs+3)*w - Q)/(qs-1),
         -w, Fs(2), 1/2*qs+1)
# entry source: odd pass-2 boundary "We need to do" (A,B,C), draft 1250-1252
p2_bd = (-(qs^4-(qs^2+1)*w+qs)/(qs-1),
         -(qs^3+(qs^3-qs^2+qs-2)*w-qs^2+qs)/(qs^2-qs),
         -w/qs^2)

def check_conc(srcABC, dstABC, nv, label):   # concrete-only (for the entry junction)
    sc = tuple(conc(x, nv, 0) for x in srcABC)
    As,Bs,Cs,k,a,D = nextABC(*sc)
    con = (As,Bs,Cs)==tuple(conc(x,nv,0) for x in dstABC)
    print("  %-26s concrete NextABC: %-5s  %s" % (label, con, "OK" if con else "*** FAIL"))
    RESULTS.append((label, con)); return con

print("=== ODD BRIDGE (7 tuples) ===")
okb = check_conc(p2_bd, br[1][:3], 13, "odd  pass2-bd -> bridge1")
for r in range(1, 7):
    okb &= check(br[r], br[r+1], 13, 0, "odd  bridge%d -> bridge%d" % (r, r+1))
okb &= check(br[7], p1_m2, 13, 0, "odd  bridge7 -> pass1(m=2)")
print("  --> %s" % ("ALL OK" if okb else "FAILURES"))

def at_u(t, uval):    # specialise a generic tuple to a fixed j (u = q^{2j})
    return tuple(Fs(x).subs({u: uval}) for x in t)

# ==================== EVEN PASS 1: j=0 special chain (r=1..6) ============
# Draft 374-471.  r1..r5 special->special ; r6 special -> r7 generic at u=1.
s1 = {}
s1[1] = (-w/qs^2, -((qs^2-3*qs+1)*w + Q)/(qs-1), w*qs^3, -w/qs^2, -(Q-w)/(qs-1))
s1[2] = (((qs^2-2*qs+2)*w+Q*qs-2*Q)/(qs-1), ((qs^2-3*qs+3)*w-Q)/(qs-1), -w, Fs(2), 1/2*qs+1)
s1[3] = (-(Q*qs^2+(qs^3-2*qs^2+2*qs-4)*w+2*Q*qs)/(8*(qs^2-qs)),
         (Q*qs^2+(qs^3-2*qs^2+4*qs-2)*w-2*Q)/(2*(qs-1)),
         -(Q*qs^3-2*Q*qs^2+(qs^4-2*qs^3+2*qs^2)*w)/(2*(qs-1)), Fs(1/4), -1/2*qs+1)
s1[4] = (2*w/qs^3, -((qs^3-qs^2+3*qs-4)*w+Q*qs)/(qs^2-qs),
         (Q*qs^3+2*Q*qs^2+(qs^4-2*qs^3+2*qs^2-4*qs)*w)/(2*(qs-1)),
         2*w/qs^3, -(Q*qs-w)/(qs^2-qs))
s1[5] = ((Q^2*qs-(qs^3-qs^2+2*qs-1)*w)/(qs^2-qs), ((qs^3-qs^2+3*qs-2)*w-Q*qs)/(qs^2-qs),
         -w/qs, Fs(-1), qs+1)
s1[6] = ((Q*qs^2-(qs^2+1)*w+Q*qs)/(qs-1), -(2*Q*qs^3-(2*qs^3-qs^2+3*qs-1)*w+Q)/(qs-1),
         (Q^2*qs^2-(qs^4-qs^3+2*qs^2-qs)*w)/(qs-1), -qs, Q)

def run_special(name, sp, last, gen_next, uval, N):
    print("=== %s (j-special chain) ===" % name)
    ok = True
    for r in range(1, last):
        ok &= check(sp[r], sp[r+1], N, 0, "%s  s%d -> s%d" % (name, r, r+1))
    ok &= check(sp[last], at_u(gen_next, uval), N, 0, "%s  s%d -> generic" % (name, last))
    print("  --> %s" % ("ALL OK" if ok else "FAILURES"))
    RESULTS.append((name, ok)); return ok

run_special("EVEN PASS 1 j=0", s1, 6, gp1[7], Fs(1), 12)

# ==================== EVEN PASS 2: j=0 special chain (r=1..5) ============
s2 = {}
s2[1] = ((Q*w+2*qs^2-5*qs+2)/(8*(qs-1)), (2*qs^3+Q*w*qs-3*qs^2+2*qs-2)/(2*(qs-1)),
         (2*qs^4-qs^3+(Q*qs^2-4*Q)*w+2*qs^2)/(2*(qs-1)), Fs(-1/4), 3/2*qs+1)
s2[2] = (2*(2*qs^3+(Q*qs+Q)*w-2*qs^2-2*qs)/(qs^2-qs), -(4*qs^3+(2*Q*qs+Q)*w-7*qs^2-qs+1)/(qs-1),
         (2*qs^4-5*qs^3+Q*w*qs^2+2*qs^2)/(2*(qs-1)), Fs(4), -2*qs+1)
s2[3] = (1/2*Q*w/qs^3, (Q*w-Q*qs)/(qs^2-qs),
         -(2*qs^4-2*qs^3+(Q*qs^2+Q*qs)*w-2*qs^2)/(2*(qs-1)), 1/2*w/qs^3, (w-qs)/(qs^2-qs))
s2[4] = ((2*qs^3+(Q*qs+Q)*w-2*qs^2-2*qs)/(4*(qs^2-qs)), (Q*w-Q*qs)/(qs^2-qs),
         -Q*w/qs, Fs(1/2), -2*qs+1)
s2[5] = (-2*(Q*w+2*qs^2-5*qs+2)/(qs-1), -(4*qs^3+(2*Q*qs+Q)*w-7*qs^2-qs+1)/(qs-1),
         -(2*qs^4-2*qs^3+(Q*qs^2+Q*qs)*w-2*qs^2)/(2*(qs-1)), Fs(4), 3/2*qs+1)
run_special("EVEN PASS 2 j=0", s2, 5, gp2[6], Fs(1), 12)

# ==================== EVEN PASS 3: j=0 (r=1..9) and j=1 (r=1..4) =========
e30 = {}
e30[1] = (-(Q*qs^2-(qs^2+1)*w+Q*qs)/(qs-1), -((qs^3-qs^2+qs-2)*w+Q*qs)/(qs^2-qs), -w/qs^2, qs, Q)
e30[2] = ((Q^2*qs-(qs^3-qs^2+2*qs-1)*w)/(qs^2-qs), -(2*Q*qs^3-(2*qs^3-qs^2+3*qs-1)*w+Q)/(qs-1),
          (Q*qs^4+Q*qs^3-(qs^4+qs^2)*w)/(qs-1), Fs(-1), qs+1)
e30[3] = (-w/qs^3, ((qs^3-qs^2+3*qs-2)*w-Q*qs)/(qs^2-qs),
          (Q^2*qs^2-(qs^4-qs^3+2*qs^2-qs)*w)/(qs-1), -w/qs^3, -(Q*qs-w)/(qs^2-qs))
e30[4] = (-(Q*qs^2+(qs^3-2*qs^2+2*qs-4)*w+2*Q*qs)/(qs^2-qs), -((qs^3-qs^2+3*qs-4)*w+Q*qs)/(qs^2-qs),
          -w/qs, Fs(2), -1/2*qs+1)
e30[5] = (((qs^2-2*qs+2)*w+Q*qs-2*Q)/(8*(qs-1)), (Q*qs^2+(qs^3-2*qs^2+4*qs-2)*w-2*Q)/(2*(qs-1)),
          (Q*qs^3+2*Q*qs^2+(qs^4-2*qs^3+2*qs^2-4*qs)*w)/(2*(qs-1)), Fs(1/4), 1/2*qs+1)
e30[6] = (2*w/qs^2, ((qs^2-3*qs+3)*w-Q)/(qs-1),
          -(Q*qs^3-2*Q*qs^2+(qs^4-2*qs^3+2*qs^2)*w)/(2*(qs-1)), 2*w/qs^2, -(Q-w)/(qs-1))
e30[7] = (w*qs, -((qs^2-3*qs+1)*w+Q)/(qs-1), -w, w*qs, -((qs^2-3*qs+1)*w+Q)/(qs-1))
e30[8] = (w/qs^2, -((qs^2-3*qs+1)*w+Q)/(qs-1), -w*qs^3, w/qs^2, -(Q-w)/(qs-1))
e30[9] = (((qs^2-2*qs+2)*w+Q*qs-2*Q)/(qs-1), ((qs^2-3*qs+3)*w-Q)/(qs-1), -w, Fs(2), 1/2*qs+1)
e31 = {}
e31[1] = (-(Q*qs^2+(qs^3-2*qs^2+2*qs-4)*w+2*Q*qs)/(8*(qs^2-qs)),
          (Q*qs^2+(qs^3-2*qs^2+4*qs-2)*w-2*Q)/(2*(qs-1)),
          -(Q*qs^3-2*Q*qs^2+(qs^4-2*qs^3+2*qs^2)*w)/(2*(qs-1)), Fs(1/4), -1/2*qs+1)
e31[2] = (2*w/qs^3, -((qs^3-qs^2+3*qs-4)*w+Q*qs)/(qs^2-qs),
          (Q*qs^3+2*Q*qs^2+(qs^4-2*qs^3+2*qs^2-4*qs)*w)/(2*(qs-1)), 2*w/qs^3, -(Q*qs-w)/(qs^2-qs))
e31[3] = ((Q^2*qs-(qs^3-qs^2+2*qs-1)*w)/(qs^2-qs), ((qs^3-qs^2+3*qs-2)*w-Q*qs)/(qs^2-qs),
          -w/qs, Fs(-1), qs+1)
e31[4] = ((Q*qs^2-(qs^2+1)*w+Q*qs)/(qs-1), -(2*Q*qs^3-(2*qs^3-qs^2+3*qs-1)*w+Q)/(qs-1),
          (Q^2*qs^2-(qs^4-qs^3+2*qs^2-qs)*w)/(qs-1), -qs, Q)
print("=== EVEN PASS 3 (j=0 chain r=1..9, then j=1 chain r=1..4) ===")
ok = True
for r in range(1, 9):
    ok &= check(e30[r], e30[r+1], 14, 0, "even p3 j=0  s%d -> s%d" % (r, r+1))
ok &= check(e30[9], e31[1], 14, 0, "even p3 j=0  s9 -> j=1 s1")
for r in range(1, 4):
    ok &= check(e31[r], e31[r+1], 14, 1, "even p3 j=1  s%d -> s%d" % (r, r+1))
ok &= check(e31[4], at_u(gp3[5], qs^2), 14, 1, "even p3 j=1  s4 -> generic")
print("  --> %s" % ("ALL OK" if ok else "FAILURES")); RESULTS.append(("EVEN PASS 3 special", ok))

# ==================== ODD PASS 2: j=0 special chain (r=1..3) =============
o2 = {}
o2[1] = ((Q*w-qs)/(qs-1), -((Q*qs-2*Q)*w+Q*qs)/(qs^2-qs), -Q*w/qs^2, qs, Q)
o2[2] = (-Q*w/qs, ((2*Q*qs-Q)*w-Q)/(qs-1), (qs^3-Q*w*qs^2)/(qs-1), -w/qs, ((2*qs-1)*w-1)/(qs-1))
o2[3] = (-(Q*w-qs)/(qs-1), ((2*Q*qs-Q)*w-Q)/(qs-1), -Q*w*qs, -qs, Q)
run_special("ODD PASS 2 j=0", o2, 3, go2[4], Fs(1), 13)

print("\n" + "="*60)
print("SECTIONS: %d   (all: %s)"
      % (len(RESULTS), "GREEN" if all(o for _,o in RESULTS) else "FAILURES"))
print("Coverage: even passes 1,2,3 (generic + j=0/j=1 specials);")
print("          odd pass 1 (= even pass 1, formulas identical);")
print("          odd pass 2 (generic + j=0 specials); odd 7-tuple bridge.")
print("          Pass<->pass boundaries: the step m=B-1 -> B is inside a pass's")
print("          generic range (a generic identity above), and junction VALUES")
print("          pass(k+1)[m=1]==pass(k)[boundary] are checked in junc.sage.")
print("Each transition: symbolic Step 3 (=> all n,j) + concrete NextABC guard.")
print("SUMMARY:", "ALL GREEN" if all(o for _,o in RESULTS) else "FAILURES")
