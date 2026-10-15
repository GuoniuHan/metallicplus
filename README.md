# Hankel determinants for the (n+2)-shifted q-metallic numbers

**Guo-Niu Han and Emmanuel Pedon** — 2026/10/16

## Abstract

For the q-deformed metallic number Φ_n(q) we prove that the Hankel continued
fraction of the (n+2)-shifted series Φ_n^(n+2) is eventually periodic, and that
the corresponding Hankel determinant sequence Δ_j^(n+2) is 2n(n+1)-(anti)periodic
and takes only the values −2, −1, 0, 1, 2. This proves part (1) of a conjecture
of Han and Pedon. The determinant values arise as telescoping products of the
partial numerators of the Hankel continued fraction. The lengthy verifications
are carried out by symbolic computation programs, whose code is in this
repository. We emphasise that these programs give rigorous symbolic proofs,
valid for all n and j at once, rather than checks of finitely many cases.

## The full paper

[metallicplus.pdf](metallicplus.pdf)

## The programs

All checks are exact (Sage over the rationals) and symbolic in `n` and `j`:
the tuples are written with `u = q^{2j}` and `w = q^n` as free symbols (so
`q^{4j} = u^2`, `q^{n-2j} = w/u`), and no value of `n` or `j` is substituted.
Run any file with `sage <file>.sage`; the committed `*.out.txt` are the expected
outputs.

| program | what it proves | in the paper |
|---|---|---|
| [`passtables.sage`](passtables.sage) | the pass-table data (Appendices D–H) as elements of `QQ(q,u,w)`, loaded by the other programs; a compact symbolic check of Step 3 and of the junctions | Appendices D–H, §3.4 |
| [`certify_step3.sage`](certify_step3.sage) | Step 3 of `NextABC` for every transition of the orbit, as identities in `QQ(q,u,w)`; the junction identities; `b8 = (-A1, B1, -C1)` | §3.4, §3.5 |
| [`certify_steps12.sage`](certify_steps12.sage) | Steps 1 and 2 via the polynomiality criterion, on cones covering every use of every tuple; the admissibility ranges of the tables; the three exits | Lemmas 8, 9, §3.5 |
| [`certify_sign.sage`](certify_sign.sage) | `s_P = 2n(n+1)` and the two sign facts of the (anti)periodicity, for all `n >= 4` | §4.3, Lemmas 14, 15 |
| [`verify_base.sage`](verify_base.sage) | the base cases `n = 1, 2, 3`, computed from the initial triple, and their invariants | Appendices A–C, §4.3 |
| [`nextabc.sage`](nextabc.sage) | the algorithm `NextABC` over `QQ[q]`, used only by `verify_base.sage` | §3.2 |

The orbit (§3.5 of the paper) has the same shape for both parities:

```
n even:  pass 1 -> bridge 2 (c1..c5) -> pass 2 -> bridge 1 (b1..b8) -> pass 1 [m=2]
n odd :  pass 1 -> bridge 3 (d1..d3) -> pass 2 -> bridge 1 (b1..b8) -> pass 1 [m=2]
```

Pass 1, the nine rows `m = 9j+r` of pass 2, and the three `j`-free bridges are
given by the same formulas for every `n >= 4`. The parity of `n` only selects
bridge 2 or 3 — pass 1 is left where `n - 2j` is 2 or 3 — and whether pass 2 is
read at integer `j` (even `n`) or half-integer `j` (odd `n`), i.e. at the `j`
with `n - 2j` even.

### Step 3 — the recurrence for the next triple

Step 3 (eqs. (14)–(16) of the paper) is an identity in `QQ(q,u,w)`, so one
symbolic check per transition settles all `n, j`. `certify_step3.sage` walks
the whole orbit, prints each computed successor `(A', B', C')`, and names the
tuple it becomes. For odd `n`, pass 2 at half-integer `j` amounts to
`u -> q^(+-1) u`; in `passtables.sage` the odd pass 2 is *derived* from the
pass-2 rows this way, not stored.

It also proves the **junction identities**, symbolically for all `n`: pass-1
row 2 at `u = w/q^2` (even `n`), resp. row 6 at `u = w/q^3` (odd `n`), has the
`A, B, C` of the first tuple `c1` of bridge 2, resp. `d1` of bridge 3; and
pass-2 row 1 at `u = w/q^2` has the `A, B, C` of `b1`. The bridge transitions and
the return from bridge 1 to pass 1 at `m = 2` are identities in `QQ(q,w)`.
Finally it checks `b8 = (-A1, B1, -C1)`, the initial tuple up to the signs of
`A` and `C`; hence the pre-period is exactly 1.

```
sage certify_step3.sage
sage passtables.sage        # compact form of the same symbolic check
```

Outputs: [`certify_step3.out.txt`](certify_step3.out.txt),
[`passtables.out.txt`](passtables.out.txt) (ending `SUMMARY: ALL GREEN`).

### Steps 1 and 2 — the polynomiality criterion

Steps 1 and 2 (the leading data `k, a` and the polynomial `D`) are not
recomputed. By the **polynomiality criterion** (Lemma 8): if `(A,B,C)` is
admissible (`A, B, C` polynomials, `B(0)=1`, `C(0)=0`, `C != 0`) and
`D(0)=1`, `deg D <= k+1`, then `(k, a, D)` is the output of `NextABC` **iff**
the Step-3 image `A*, B*` is polynomial with `B*(0)=1`. Since Step 3 is a
symbolic identity, `A*, B*` are the `A, B` of the next tuple: the `K, D` of a
tuple are correct exactly where the tuple and the next one are both admissible.

For every pass-table tuple, walked in orbit order, `certify_steps12.sage`
proves on a cone `{ j >= j0, n-2j >= d0 }` (or `{ n >= d0 }` for `j`-free
tuples): (i) the tuple is admissible, (ii) `k >= 0`, `D(0)=1`, `deg D <= k+1`,
(iii) the Step-3 image is admissible; and it checks that the orbit uses the
tuple only inside that cone (Lemma 9). Polynomiality is proved in two parts: the
`(q-1)` denominators cancel identically in `(n,j)` (expansion at `q = 1+eps`
with `n, j` symbolic), and every block `P_{b,c}(q) u^b w^c` has q-order
`val_q P + 2jb + nc >= 0`, an affine inequality in `(n,j)` checked on the cone
by the finite test (21) of the paper. The program also certifies the
admissibility ranges printed in the tables, `p = (0,1,3,2,0,0,4,3,1)` (pass 1)
and `p' = (0,3,2,0,0,2,4,3,1)` (pass 2), and the three exits (pass-1 row 3 at
`n-2j=2`, pass-1 row 7 at `n-2j=3`, pass-2 row 2 at `n-2j=2` have
`A = c q^{-1}`).

```
sage certify_steps12.sage
```

Output: [`certify_steps12.out.txt`](certify_steps12.out.txt), ending
`STEPS 1 & 2 PROVED UNIFORMLY for ALL (n,j)`.

### The (anti)periodicity

With `L = 2n(n+1)` and `P` the period, the shift lemma (Lemma 14) gives
`Delta_{s_{j+P}} = (-prod_{i<P} v_i)^{s_j} Delta_L Delta_{s_j}`, provided
`s_P = L`. Lemma 15 gives the two facts that yield `Delta_{h+L} = (-1)^n Delta_h`:
(I) `prod_{i<P} v_i = -1` and (II) `Delta_L = (-1)^n`, i.e.
`X(n) = eps_P + sum_{v_i<0} s_i = n (mod 2)`.

`certify_sign.sage` proves `s_P = L`, (I) and (II) for **all n >= 4**: along one
period every `k` is affine in `t` (`n = 2t` or `2t+1`) and in the block number
`j`, so all sums are computed exactly by symbolic summation over the segments
of the orbit. It finds `P = 9n-10` resp. `9n-13`, `s_P = 2n(n+1)`,
`sum e = 0`, `#{a > 0} = 12t-7` resp. `12t-5`, and

```
X(2t)   = 160/3 t^3 - 24 t^2 + 2/3 t
X(2t+1) = 160/3 t^3 + 40 t^2 + 2/3 t - 1
```

and checks that `(X(n) - n)/2` is integer-valued (integer at `deg+1`
consecutive integers, by Newton's forward differences).

```
sage certify_sign.sage
```

Output: [`certify_sign.out.txt`](certify_sign.out.txt), ending
`RESULT: for ALL n >= 4: ...`.

### Base cases n = 1, 2, 3

`NextABC` runs verbatim at a numerical `n`, so the base-case orbits are not
guessed but computed: `verify_base.sage` iterates from the initial triple, prints
each orbit (the tuples of Appendices A–C), and asserts the invariants used in
the paper: pre-period 1; period 2, 9, 14; the last tuple of the period is
`(-A1, B1, -C1)`; `sum(k+1) = 2n(n+1)` over one period; and the two sign facts
`prod_{i<P} v_i = -1` and `X(n) = n mod 2`.

```
sage verify_base.sage
```

Output: [`verify_base.out.txt`](verify_base.out.txt), ending
`BASE CASES n=1,2,3 (computed from the initial triple): ALL OK`.
