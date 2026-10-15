# Pass-table data of the paper (Appendices D-H) and a compact symbolic Step-3 checker.
# Variables: w = q^n, u = q^{2j}  (q^{4j}=u^2, q^{n-2j}=w/u, q^{2j+c}=u q^c, ...).
# Every tuple entry is an element of Q(q,u,w) with denominator lambda*q^s*(q-1)^e*u^b*w^c.
# The (K,D) of each tuple are those printed in the paper; Steps 1,2 are certified
# in certify_steps12.sage.  Step 3 (eqs. (14)-(16) of the paper) is checked here
# to hold IDENTICALLY in Q(q,u,w)  =>  all n,j at once.

Rs = PolynomialRing(QQ, ['qs','u','w']); qs,u,w = Rs.gens(); Fs = Rs.fraction_field()
Qs = qs^2 - qs + 1

def split_K(K):
    K = Fs(K); a = K.subs({qs:1, u:1, w:1}); return a, K/a     # a, q^k

def step3(A,B,C,K,D):
    a, qk = split_K(K)
    AA = (-D^2*A/a + B*D*qk - C*a*qk^2) / (qk^2 * qs^2)
    BB = 2*A*D/(a*qk) - B
    CC = -A*qs^2/a
    return Fs(AA), Fs(BB), Fs(CC)

def check(src, dst, label):
    # dst is the symbolic successor, expressed in (u,w) (a j+1 wrap is baked
    # into dst via u -> q^2 u); the Step-3 identity is checked in Q(q,u,w).
    A,B,C,K,D = [Fs(x) for x in src]
    A2,B2,C2,K2,D2 = [Fs(x) for x in dst]
    AA,BB,CC = step3(A,B,C,K,D)
    sym = (AA==A2 and BB==B2 and CC==C2)
    print("  %-26s symbolic Step3: %-5s  %s" % (label, sym, "OK" if sym else "*** FAIL"))
    return sym

# ============================ EVEN PASS 1 (generic block) ================
# r = 1..9, generic j (>=1 for r<=6, all j for r=7,8,9).
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
def run_generic(name, gp):
    print("=== %s (generic block, all j) ===" % name)
    ok = True
    for r in range(1, 9):
        ok &= check(gp[r], gp[r+1], "%s  r=%d -> r=%d" % (name, r, r+1))
    ok &= check(gp[9], shift_j1(gp[1]), "%s  r=9 -> r=1(j+1)" % name)
    print("  --> %s" % ("ALL OK" if ok else "FAILURES"))
    RESULTS.append((name, ok))
    return ok

run_generic("PASS 1", gp1)

# ============================ EVEN PASS 2 (generic block) ================
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
run_generic("PASS 2 rows m=9j+r", gp2)

# odd pass 1 formulas are IDENTICAL to even pass 1 (verified by diff) -> covered.

# ============================ ODD PASS 2 (derived, no new data) ==========
# Pass 2 is ONE generic family gp2 = pass-2 rows 1..9 for both parities.  For odd n the
# tuple at pass-2 index m is the generic row at the half-integer index m+5/2:
#   m=9j+r  ->  row r-2 at j+1/2  (3<=r<=9),   row r+7 at j-1/2  (r=1,2),
# i.e. u=q^{2j} -> q^{+1} u resp. q^{-1} u.  go2 is DEFINED this way; its
# transitions are then re-checked below (symbolically).
def _half(t, c):  return tuple(Fs(x).subs({u: u*qs^c}) for x in t)
go2 = {}
for r in range(1, 10):
    go2[r] = _half(gp2[r-2], 1) if r >= 3 else _half(gp2[r+7], -1)
run_generic("PASS 2 odd (index m+5/2)", go2)

# ====================== BRIDGE 1 (b1..b8, w-only, BOTH parities) ==========
# j-free => no u, and the same formulas for even and odd n.  br[1] is the
# pass-2 boundary tuple: its (A,B,C) is the generic pass-2 row r_B at the last
# block -- even: gp2[1] at u=w/q^2;  odd: go2[3] at u=w/q^3 (both checked in
# the JUNCTIONS section below) -- but its Steps-1,2 data are (K,D)=(q,Q), not
# the generic (q,1-q).  After br[8] the orbit re-enters pass 1 at m=2.
br = {}
br[1] = (-(qs^4-(qs^2+1)*w+qs)/(qs-1),
         -(qs^3+(qs^3-qs^2+qs-2)*w-qs^2+qs)/(qs^2-qs),
         -w/qs^2,
         qs, Q)
br[2] = ((qs^4-2*qs^3+3*qs^2-2*qs+1)/(qs-1) + ((-qs^3+qs^2-2*qs+1)/(qs^2-qs))*w,
         (-2*qs^5+2*qs^4-2*qs^3-qs^2+qs-1)/(qs-1) + ((2*qs^3-qs^2+3*qs-1)/(qs-1))*w,
         (qs^6+qs^3)/(qs-1) + ((-qs^4-qs^2)/(qs-1))*w,
         Fs(-1), qs+1)
br[3] = ((-1/qs^3)*w,
         (-qs^2+qs-1)/(qs-1) + ((qs^3-qs^2+3*qs-2)/(qs^2-qs))*w,
         (qs^6-2*qs^5+3*qs^4-2*qs^3+qs^2)/(qs-1) + ((-qs^4+qs^3-2*qs^2+qs)/(qs-1))*w,
         -w/qs^3, (-qs^2+qs-1)/(qs-1) + (1/(qs^2-qs))*w)
br[4] = ((-qs^3-qs^2+qs-2)/(qs-1) + ((-qs^3+2*qs^2-2*qs+4)/(qs^2-qs))*w,
         (-qs^2+qs-1)/(qs-1) + ((-qs^3+qs^2-3*qs+4)/(qs^2-qs))*w,
         (-1/qs)*w,
         Fs(2), -1/2*qs+1)
br[5] = ((1/8*qs^3-3/8*qs^2+3/8*qs-1/4)/(qs-1) + ((1/8*qs^2-1/4*qs+1/4)/(qs-1))*w,
         (1/2*qs^4-1/2*qs^3-1/2*qs^2+qs-1)/(qs-1) + ((1/2*qs^3-qs^2+2*qs-1)/(qs-1))*w,
         (1/2*qs^5+1/2*qs^4-1/2*qs^3+qs^2)/(qs-1) + ((1/2*qs^4-qs^3+qs^2-2*qs)/(qs-1))*w,
         Fs(1/4), 1/2*qs+1)
br[6] = ((2/qs^2)*w,
         (-qs^2+qs-1)/(qs-1) + ((qs^2-3*qs+3)/(qs-1))*w,
         (-1/2*qs^5+3/2*qs^4-3/2*qs^3+qs^2)/(qs-1) + ((-1/2*qs^4+qs^3-qs^2)/(qs-1))*w,
         2*w/qs^2, (-qs^2+qs-1)/(qs-1) + (1/(qs-1))*w)
br[7] = (qs*w,
         (-qs^2+qs-1)/(qs-1) + ((-qs^2+3*qs-1)/(qs-1))*w,
         -w,
         qs*w, (-qs^2+qs-1)/(qs-1) + ((-qs^2+3*qs-1)/(qs-1))*w)
br[8] = ((1/qs^2)*w,
         (-qs^2+qs-1)/(qs-1) + ((-qs^2+3*qs-1)/(qs-1))*w,
         -qs^3*w,
         w/qs^2, (-qs^2+qs-1)/(qs-1) + (1/(qs-1))*w)
# exit target: pass 1, m=2 (j=0)  [even p1 r=2 j=0; odd p1 identical]
p1_m2 = (((qs^2-2*qs+2)*w + Q*qs - 2*Q)/(qs-1),
         ((qs^2-3*qs+3)*w - Q)/(qs-1),
         -w, Fs(2), 1/2*qs+1)

print("=== BRIDGE 1 (b1..b8, both parities) ===")
okb = True
for r in range(1, 8):
    okb &= check(br[r], br[r+1], "bridge%d -> bridge%d" % (r, r+1))
okb &= check(br[8], p1_m2, "bridge8 -> pass1(m=2)")
print("  --> %s" % ("ALL OK" if okb else "FAILURES"))
RESULTS.append(("BRIDGE 1", okb))

def at_u(t, uval):    # specialise a generic tuple to a fixed j (u = q^{2j})
    return tuple(Fs(x).subs({u: uval}) for x in t)

# ==================== EVEN PASS 1: j=0 special chain (r=1..6) ============
# r1..r5 special->special ; r6 special -> r7 generic at u=1.
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

def run_special(name, sp, last, gen_next, uval):
    print("=== %s (j-special chain) ===" % name)
    ok = True
    for r in range(1, last):
        ok &= check(sp[r], sp[r+1], "%s  s%d -> s%d" % (name, r, r+1))
    ok &= check(sp[last], at_u(gen_next, uval), "%s  s%d -> generic" % (name, last))
    print("  --> %s" % ("ALL OK" if ok else "FAILURES"))
    RESULTS.append((name, ok)); return ok

run_special("PASS 1 j=0", s1, 6, gp1[7], Fs(1))

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
run_special("BRIDGE 2 c1..c5 (n even)", s2, 5, gp2[6], Fs(1))

# ==================== ODD PASS 2: j=0 special chain (r=1..3) =============
o2 = {}
o2[1] = ((Q*w-qs)/(qs-1), -((Q*qs-2*Q)*w+Q*qs)/(qs^2-qs), -Q*w/qs^2, qs, Q)
o2[2] = (-Q*w/qs, ((2*Q*qs-Q)*w-Q)/(qs-1), (qs^3-Q*w*qs^2)/(qs-1), -w/qs, ((2*qs-1)*w-1)/(qs-1))
o2[3] = (-(Q*w-qs)/(qs-1), ((2*Q*qs-Q)*w-Q)/(qs-1), -Q*w*qs, -qs, Q)
run_special("BRIDGE 3 d1..d3 (n odd)", o2, 3, go2[4], Fs(1))

# ==================== JUNCTIONS (symbolic, all n) =======================
# A pass ends at its boundary index B = 9j_B + r_B, with j_B = n/2-1 (even n,
# u = q^{2j_B} = w/q^2) or j_B = (n-3)/2 (odd n, u = w/q^3).  The step
# m = B-1 -> B is a generic transition (its Step-3 identity is checked above,
# for all u,w), so the tuple at B has (A,B,C) = generic row r_B at u = u_B.
# Its Steps-1,2 data are NOT those of the generic row: the tuple at B is the
# first tuple of the next pass (or of the bridge).  The value identity
#     row r_B (A,B,C) at u=u_B  ==  next pass, m=1 (A,B,C)
# is an identity in QQ(q,w): proved here for all n, no value substituted.
def junction(label, gen_row, uB, dst):
    lhs = tuple(Fs(x).subs({u: uB}) for x in gen_row[:3])
    ok = (lhs == tuple(Fs(x) for x in dst[:3]))
    print("  %-46s : %s" % (label, "True  (identity in q, w=q^n)" if ok else "*** FAIL"))
    RESULTS.append((label, ok)); return ok

print("=== JUNCTIONS: leaving a pass  (symbolic) ===")
junction("EVEN P1 row 2, u=w/q^2  ==  bridge 2, c1",  gp1[2], w/qs^2, s2[1])
junction("ODD  P1 row 6, u=w/q^3  ==  bridge 3, d1",  gp1[6], w/qs^3, o2[1])
junction("BOTH pass-2 row 1, u=w/q^2  ==  bridge 1, b1", gp2[1], w/qs^2, br[1])

print("\n" + "="*60)
print("SECTIONS: %d   (all: %s)"
      % (len(RESULTS), "GREEN" if all(o for _,o in RESULTS) else "FAILURES"))
print("Coverage: pass 1 (generic + j=0 specials), both parities;")
print("          pass 2 rows m=9j+r (both parities; odd n at half-integer j);")
print("          bridge 1 (b1..b8), bridge 2 (c1..c5), bridge 3 (d1..d3): j-free, valid for all n.")
print("          Pass<->pass boundaries: the step m=B-1 -> B is inside a pass's")
print("          generic range (a generic identity above), and the junction")
print("          VALUES pass(k)[boundary]==pass(k+1)[m=1] are symbolic identities.")
print("Each transition: symbolic Step 3 identity in Q(q,u,w) (=> all n,j).")
print("Orbit: P1 -> Bridge 2 (n even) / Bridge 3 (n odd) -> P2 -> Bridge 1 -> P1[m=2].")
print("SUMMARY:", "ALL GREEN" if all(o for _,o in RESULTS) else "FAILURES")
