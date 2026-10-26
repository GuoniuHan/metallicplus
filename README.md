# Hankel determinants for the (n+2)-shifted q-metallic numbers

**Guo-Niu Han and Emmanuel Pedon** — 2026/10/26

## Abstract

Let Φ_n(q) denote the q-deformation (in the sense of Morier-Genoud & Ovsienko)
of the metallic number φ_n = (n + √(n²+4))/2. This is a power series with
integer coefficients. We prove that the Hankel continued fraction of the
(n+2)-shifted series Φ_n^(n+2) is eventually periodic, and that the
corresponding Hankel determinant sequence Δ^(n+2) is 2n(n+1)-periodic if n is
even, 2n(n+1)-antiperiodic if n is odd, and that it takes only the values
−2, −1, 0, 1, 2. This confirms part of a former conjecture of ours and
complements similar results we obtained for all ℓ-shifts of Φ_n with
0 ≤ ℓ ≤ n+1. In addition, we formulate a new conjecture of quasi-polynomiality
for higher shifts ℓ ≥ n+3.

The determinant values arise as telescoping products of the partial numerators
of the Hankel continued fraction. Most of the technically involved and lengthy
verifications are carried out by the symbolic computation programs of this
repository. They give rigorous symbolic proofs, valid for all n and j at once,
rather than checks of finitely many cases.

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
| [`passtables.sage`](passtables.sage) | the pass-table data (Appendices D–H) as elements of `QQ(q,u,w)`, loaded by the other programs; a compact symbolic check of Step 3 and of the junctions | Appendices D–H, §3.3, §3.4 |
| [`certify_step3.sage`](certify_step3.sage) | Step 3 of `NextABC` for every step of the sequence of quintuples, as identities in `QQ(q,u,w)`; the junction identities; `b8 = (-A1, B1, -C1)` | condition (S3) of Corollary 3.2, Proposition 3.3, eq. (3.7), Proposition 3.5 |
| [`certify_steps12.sage`](certify_steps12.sage) | Steps 1 and 2 via the polynomiality criterion, on cones covering every use of every tuple; the validity ranges of the tables; the three exits | Lemma 3.1, condition (S12) of Corollary 3.2, Proposition 3.3, Remark 3.4 |
| [`certify_sign.sage`](certify_sign.sage) | `s_P = 2n(n+1)` and the two sign facts of the (anti)periodicity, for all `n >= 4` | §4.2, Lemmas 4.2 and 4.4 |
| [`verify_base.sage`](verify_base.sage) | the base cases `n = 1, 2, 3`, computed from the initial triple, and their invariants | Appendices A–C, §3.2, Lemmas 4.2 and 4.4 |
| [`nextabc.sage`](nextabc.sage) | the algorithm `NextABC` over `QQ[q]`, used only by `verify_base.sage` | §2.1, Algorithm 2.3 |

The sequence of quintuples (§3.3 of the paper) has the same shape for both parities:

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

Step 3 (eqs. (2.7)–(2.9) of the paper) is an identity in `QQ(q,u,w)`, so one
symbolic check per step settles all `n, j`. `certify_step3.sage` walks
the whole sequence, prints each computed successor `(A', B', C')`, and names the
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
recomputed. By the **polynomiality criterion** (Lemma 3.1): if `(A,B,C)`
satisfies (3.4) (`A, B, C` polynomials, `B(0)=1`, `C(0)=0`), `C != 0`, and the
tuple satisfies (3.5) (`k >= 0`, `D(0)=1`, `deg D <= k+1`), then `(k, a, D)` is
the output of `NextABC` **iff** the Step-3 image `A*, B*` is polynomial with
`B*(0)=1`. Since Step 3 is a symbolic identity, `A*, B*` are the `A, B` of the
next tuple: the `K, D` of a tuple are those of `NextABC` exactly where the
triples of the tuple and of the next one both satisfy (3.4) (Corollary 3.2).

For every pass-table tuple, walked in the order of the sequence,
`certify_steps12.sage` proves on a cone `{ j >= j0, n-2j >= d0 }` (or
`{ n >= d0 }` for `j`-free tuples): (i) its triple satisfies (3.4), (ii) it
satisfies (3.5), (iii) the Step-3 image satisfies (3.4); and it checks that the
sequence uses the tuple only inside that cone (Proposition 3.3, "Coverage").
Polynomiality is proved in two parts: the
`(q-1)` denominators cancel identically in `(n,j)` (expansion at `q = 1+eps`
with `n, j` symbolic), and every block `P_{b,c}(q) u^b w^c` has q-order
`val_q P + 2jb + nc >= 0`, an affine inequality in `(n,j)` checked on the cone
by the finite test (3.9) of the paper. For odd `n` the program walks pass 2 by
the integer index of `go2` (paper index `m+5/2`); each such line also names the
row of Appendix E at half-integer `j` that it is. The program also certifies the
ranges `n - 2j >= h_r` printed in the table headers (where the triple of each row satisfies
(3.4)), `h = (0,1,3,2,0,0,4,3,1)` (pass 1)
and `h' = (0,3,2,0,0,2,4,3,1)` (pass 2), and the three exits (pass-1 row 3 at
`n-2j=2`, pass-1 row 7 at `n-2j=3`, pass-2 row 2 at `n-2j=2` have
`A = c q^{-1}`: this is where a pass ends, Remark 3.4).

```
sage certify_steps12.sage
```

Output: [`certify_steps12.out.txt`](certify_steps12.out.txt), ending
`STEPS 1 & 2 PROVED UNIFORMLY for ALL (n,j)`.

### The (anti)periodicity

With `L = 2n(n+1)` and `P` the period, `s_P = L` (Lemma 4.2), and the periodicity
of the data gives (Lemma 4.3)
`Delta_{s_j+L} = (-prod_{i<P} v_i)^{s_j} Delta_L Delta_{s_j}`. Lemma 4.4 gives
the two facts that yield `Delta_{h+L} = (-1)^n Delta_h`:
(i) `prod_{i<P} v_i = -1` and (ii) `Delta_L = (-1)^n`, i.e.
`theta(n) = eps_P + sum_{v_i<0} s_i = n (mod 2)`. Here `s_i`, `eps_P` are those of
the H-fraction, with exponents `sigma_i = k_{i+1}` (`k_m = val A_m`).

`certify_sign.sage` proves `s_P = L` (Lemma 4.2), (i) and (ii) (Lemma 4.4) for **all n >= 4**: along one
period every `k` is affine in `t` (`n = 2t` or `2t+1`) and in the block number
`j`, so all sums are computed exactly by symbolic summation over the segments
of the sequence. It finds `P = 9n-10` resp. `9n-13`, `s_P = 2n(n+1)`,
`sum e = 0`, `#{a > 0} = 12t-7` resp. `12t-5`, and

```
theta(2t)   = 160/3 t^3 - 24 t^2 + 2/3 t
theta(2t+1) = 160/3 t^3 + 40 t^2 + 2/3 t - 1
```

and checks that `(theta(n) - n)/2` is integer-valued (integer at `deg+1`
consecutive integers, by Newton's forward differences).

```
sage certify_sign.sage
```

Output: [`certify_sign.out.txt`](certify_sign.out.txt), ending
`RESULT: for ALL n >= 4: ...`.

### Base cases n = 1, 2, 3

`NextABC` runs verbatim at a numerical `n`, so the base-case sequences are not
guessed but computed: `verify_base.sage` iterates from the initial triple, prints
each sequence of quintuples (the tuples of Appendices A–C), and asserts the invariants used in
the paper: pre-period 1; period 2, 9, 14; the last tuple of the period is
`(-A1, B1, -C1)`; `sum(k+1) = 2n(n+1)` over one period; and the two sign facts
`prod_{i<P} v_i = -1` and `theta(n) = n mod 2`.

```
sage verify_base.sage
```

Output: [`verify_base.out.txt`](verify_base.out.txt), ending
`BASE CASES n=1,2,3 (computed from the initial triple): ALL OK`.
