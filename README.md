# The Hankel continued fraction of the (n+2)-shifted q-metallic numbers

**Guo-Niu Han** — 2026/07/12

## Abstract

For the q-deformed metallic number Φ_n(q) we prove that the Hankel continued
fraction of the (n+2)-shifted series Φ_n^(n+2) is eventually periodic, and that
the corresponding Hankel determinant sequence Δ_j^(n+2) is 2n(n+1)-(anti)periodic
and takes only the values −2, −1, 0, 1, 2. This proves part (1) of a conjecture
of Han and Pedon. The determinant values arise as telescoping products of the
partial numerators of the Hankel continued fraction. Most of the technically
involved and lengthy verifications are carried out by a symbolic computation
program, whose code is provided in this repository for independent verification.
We emphasize that the program delivers rigorous symbolic proofs — valid for all
n and j at once — rather than merely checking finitely many initial terms.

## The full paper

[metallicplus.pdf](metallicplus.pdf)

## The programs

All checks are exact (Sage over the rationals); nothing is sampled numerically
except explicit concrete guards. Run any file with `sage <file>.sage`; the
committed `*.out.txt` are the expected outputs.

The pass-table data — every tuple written as an element of `QQ(q,u,w)` with
`u = q^{2j}`, `w = q^n` (so `q^{4j}=u^2`, `q^{n-2j}=w/u`) — and the shared
machinery live in [`passtables.sage`](passtables.sage), loaded by the `certify_*`
programs. [`nextabc.sage`](nextabc.sage) is the algorithm `NextABC` over `QQ[q]`,
used for the concrete cross-checks.

## Verification

The proof expands Φ_n^(n+2) into a Hankel continued fraction by iterating
`NextABC`, whose one-step map has three steps. Each step is verified
**symbolically, for all n and j at once** — never by sampling initial terms.

### Steps 1 and 2 — the leading data and the truncation

For every pass-table tuple, `certify_steps12.sage` verifies `k = val A`,
`a = lc(A)` (Step 1) and `D = [a q^k B/A]_{<= k+1}` (Step 2). Writing each entry
in blocks `P_{b,c}(q) u^b w^c`, the q-order `val_q P + 2jb + nc` is affine in
`(n,j)`, so every claim reduces to a finite set of affine inequalities on a cone
`{ j >= j0, n-2j >= N }`. The output walks the pass-table in order, printing, for
each tuple, its type, blocks, `k, a, D`, and the checks.

```
sage certify_steps12.sage
```

Output: [`certify_steps12.out.txt`](certify_steps12.out.txt), ending
`STEPS 1 & 2 PROVED UNIFORMLY for ALL (n,j)`.

### Step 3 — the recurrence for the next triple

Step 3 is a rational-function identity in `q` (with `u, w` free), so one symbolic
check per transition settles all `n, j`. `certify_step3.sage` walks the whole
orbit, prints each computed successor `(A', B', C')`, and names the tuple it
becomes:

```
Even:  P1 -> P2 -> P3 -> (P4 = P2)
Odd:   P1 -> P2 -> bridge -> P1
```

```
sage certify_step3.sage
```

Output: [`certify_step3.out.txt`](certify_step3.out.txt). A compact form of the
same check, with a concrete `NextABC` guard at one `(n, j)` per transition, is
run directly from the data file:

```
sage passtables.sage
```

### Base cases n = 1, 2, 3

`NextABC` runs verbatim at a numerical `n`, so the base-case orbits are not
guessed but computed: `verify_base.sage` iterates from the initial triple, prints
each orbit (the tuples of the appendices), and checks the structural invariants
(pre-period 1; period 2, 9, 14; `sum(k+1) = 2n(n+1)` over one period).

```
sage verify_base.sage
```

Output: [`verify_base.out.txt`](verify_base.out.txt).
