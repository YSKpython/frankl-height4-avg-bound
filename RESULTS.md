# Computational results

Raw output of the verification programs.

Nothing here is assumed by the proofs in the paper except where explicitly
stated. Theorem 6.1 (`n ≤ 10`, and `n = 11` with `t ≤ 3`) is the one result that
depends on computation for its content; the finite half of Theorem 7.10 is a
finite evaluation of the explicit function `Ψ(n,t)` of Definition 7.7, carried
out in exact integer arithmetic. Everything else below is a test of statements
that are proved in the paper, run independently of their proofs.

Machine: single core, gcc 13.3, Python 3.12.

---

## 1. Exhaustive enumeration (`exhaust_new.c`)

Pruning uses **only definitional constraints**: core member sets have size at
most `n-2`, the family is union-closed, and no chain has five member sets. None
of the paper's lemmas is presupposed, so all of them are tested. The coatom
index set `T` is fixed to a canonical `t`-subset; every quantity checked is
invariant under permutations of `[n]`, so this loses nothing, and counts are
multiplied by `C(n,t)` to obtain labelled totals.

```
  n   t    UC-families    qualifying  max q  max Phi+   bound       labelled
  4   0             64             0      0       ---       4              0
  4   1             97            35      3         6       6            140
  4   2            141            91      3         6       8            546
  4   3            250           201      3         6      10            804
  4   4            641           544      4         8      12            544
  5   0            882             0      0       ---       5              0
  5   1           1567           436      6         6       8           2180
  5   2           2736          1555      6         8      11          15550
  5   3           6345          5203      6         8      14          52030
  5   4          23146         22388      7         9      17         111940
  5   5         166953        164328     10        10      20         164328
  6   0          18734             0      0       ---       6              0
  6   1          39989          9584      2         6      10          57504
  6   2          84693         36837      4         8      14         552555
  6   3         258181        170269      4        10      18        3405380
  6   4        1339990       1144209      4        10      22       17163135
  6   5       14171508      14143677      5        10      26       84862062
```

Labelled totals: `n=4`: 2,034 · `n=5`: 346,028 · `n=6` (`t ≤ 5`): 106,040,636.
**Grand total 106,388,698 families, zero violations.**

Independent cross-checks:

* for `n = 4` a separate Python program scanning all `2^16` subfamilies of
  `2^[4]` also finds exactly 2,034 labelled families;
* `t = 0` yields no qualifying family, confirming Lemma 2.2 (`t ≥ 1`);
* `verify_h4.py`, which enumerates families by a different algorithm, reproduces
  the totals 2,034 and 346,028.

Statements checked on every family: Lemmas 3.1–3.6, Proposition 4.1,
Theorem 4.3, Lemma 5.1, Theorem 5.2, all of Section 7 (Lemmas 7.1–7.6, the
assembled local bound, `q ≤ Q(n,t)`), the residual inequality of Theorem 6.2,
and `Avg(A) ≥ n/2`.

The case `n = 6`, `t = 6` was not completed by raw enumeration (more than `10^9`
families at roughly `1.2 × 10^6` families per second); it is covered by the
small-part verification below.

---

## 2. Small-part verification (`verify_small.c`)

`Φ⁺` depends only on the member sets of size below `n/2`, so instead of
enumerating families one enumerates the possible **small parts**. Every family's
small part occurs among the enumerated states, so a bound proved here holds for
all families. A state is discarded only when it is impossible; the discard rules
are listed in the source and in Section 6 of the paper. Two of them use the
proved Lemmas 3.1, 3.3 and 3.6, which were independently confirmed by the
enumeration of Section 1 for `n ≤ 6`.

### Exact maxima (branch-and-bound cut disabled)

```
 n\t     1     2     3     4     5     6     7     8
  4      6     6     6     8     -     -     -     -
  5      6     8     8     9    10     -     -     -
  6      6     8    10    10    10    12     -     -
  7      7     7    11    13    13    13    14     -
  8      8     8    10    14    16    16    16    16
```

On the fourteen pairs `(n,t)` where Section 1 is also complete, the two
computations agree on the maximum in every case. The bound `t(n-2)+n` is attained
only at `(n,t) = (4,1)`, by the family `2^[3]\{∅} ∪ {[4]}` of Example 4.6.

### Verification (branch-and-bound cut enabled)

```
 n = 9  : t = 1..9   8·10^4 – 1·10^7 states per t   max Phi+ 19   VERIFIED
 n = 10 : t = 1..10  9·10^4 – 4·10^7 states per t   max Phi+ 22   VERIFIED
 n = 11 : t = 1,2,3  1.6·10^6 – 1.7·10^7 states     max Phi+ 11   VERIFIED
```

**Conclusion.** The residual inequality holds for every `n ≤ 10` and every `t`,
and for `n = 11` with `t ≤ 3`. This is Theorem 6.1 of the paper.

---

## 3. The closing argument (`verify_h4.py`)

### 3.1 Window evaluation of Theorem 7.10

The finite half of Theorem 7.10 evaluates `Ψ(n,t)` of Definition 7.7 for every
`(n,t)` with `n ≥ 11`, `t ≥ 3`, `n ≤ 4t+3`. The square-root term is bounded by
`isqrt` rounded upwards, so the evaluation is a chain of exact integer
comparisons with no floating-point arithmetic.

```
[window]  exact 11 <= n <= 200: violations = 0   worst Psi/target = 0.723 at (n,t) = (11,4)
```

The ratio `Ψ(n,t) / (t(n-2)+n)` decreases steadily with `n`:

```
 n      11     20     40     60     89    120    160    200
 ratio  0.723  0.491  0.369  0.316  0.292  0.233  0.205  0.185
```

The paper needs only `n ≤ 200`; the same sweep in float mode is clean to
`n = 600`.

The maximisation over `r` inside `Ψ` is done at a small set of candidate points
(the two branch boundaries and the integer peak of the concave second branch).
This was cross-checked against a **full integer scan over `1 ≤ r ≤ R`** for
every `(n, t, w₀)` with `n ≤ 120`: the candidate maximum equals the full-scan
maximum in every case, deficit zero. The integer version was also confirmed to
dominate the float version everywhere in that range.

### 3.2 The `r = 0` branch

`Ψ_B` admits `r = 0`, since the set `L` of lines through `A₀` may be empty
(Remark 7.8). Checked directly: over `11 ≤ n ≤ 120` and all `(t, w₀)`, the
maximum over `r ≥ 1` is never negative, so admitting `r = 0` changes `Ψ` only in
the degenerate case `R = ε`, where it is needed. Including it leaves the window
sweep clean.

### 3.3 Tail inequalities (`n ≥ 201`)

Every inequality used in the tail half of Theorem 7.10 is re-checked in exact
integer arithmetic for `201 ≤ n ≤ 10,000`:

```
[tail]    n=201..10000: tail inequality violations = 0
```

The inequalities are: `64n³ + 256n² ≤ (n² - 11n - 16)²`; the three chain steps
`11n + 16 ≤ n²/16`, `256n² ≤ 2n³`, `(225/256)n⁴ ≥ 66n³`; the case-(A) bound
`n² - 18n - 4 ≥ 0`; the `r = 0` branch `w₀ + ε ≤ (n² - n + 6)/4`; and
`f ≤ 5` together with the `q ≤ n+4` estimate for odd `n`.

The earlier draft started the tail at `n = 90`, where the step
`n² - 11n - 16 ≥ (7/8)n²` holds by a margin of 6.5. Moving the finite range to
`n ≤ 200` and the tail to `n ≥ 201` removes that tightness.

### 3.4 Extremal and window families

```
[construction] n= 8  UC=True sep=True h=4  t= 8 q= 8 (n-2= 6) Phi+= 16 target=  56  violations=0
[construction] n=10  UC=True sep=True h=4  t=10 q=10 (n-2= 8) Phi+= 20 target=  90  violations=0
[construction] n=12  UC=True sep=True h=4  t=12 q=12 (n-2=10) Phi+= 24 target= 132  violations=0
[construction] n=14  UC=True sep=True h=4  t=14 q=14 (n-2=12) Phi+= 28 target= 182  violations=0
[construction] n=16  UC=True sep=True h=4  t=16 q=16 (n-2=14) Phi+= 32 target= 240  violations=0
[construction] n=18  UC=True sep=True h=4  t=18 q=18 (n-2=16) Phi+= 36 target= 306  violations=0
```

These are the families of Proposition 7.12. For `n ≥ 12` they lie inside the
residual window and have `q = n > n-2`, so they refute the route through
Corollary 4.5; they also attain equality in Lemma 7.5. Several hundred further
window families were constructed from near-partitions of `[n]` into two or three
blocks, reaching `q = 14` at `n = 14`; zero violations.

### 3.5 Independent samples

```
[exhaustive] n=4: 2034 families    -> violations 0
[exhaustive] n=5: 346028 families  -> violations 0
[random]     6 <= n <= 16, ~1900 families sampled -> violations 0
n = 7: 25,509 distinct families    -> violations 0
```

---

## 4. Negative results recorded in the paper

These are the routes that were tried and failed; they are kept here because they
constrain what a different proof of the same result can look like.

* **The reduction to height three fails.** The inequality
  `Avg(A_x) ≥ (n-1)/2` for the subfamily `A_x = { A ∈ A : x ∉ A }`, which would
  have reduced the per-coatom bound to Bouchard's height-three theorem, is
  false: 213 counterexamples were found, in every instance exactly when `A_x` is
  not separating — and `A_x` is non-separating in roughly 70% of cases.
* **The weighted generalisation is false too.** `{∅, {1}, {1,2}}` has height
  three and is separating, yet for weights `w(1) = 1`, `w(2) = 100` its weighted
  average is `34 < 50.5`.
* **The counting bound `q ≤ n-2` is unreachable** inside the residual window:
  Proposition 7.12, verified above for `8 ≤ n ≤ 18`.
* **The per-coatom bound `Ctilde_x ≤ (n-2) + n/t`** was checked on 163,610
  pairs (family, coatom index) with zero violations, so it is presumably true;
  but it is strictly stronger than what `Σ_x Ctilde_x = Φ⁺` requires, and the
  closing argument of Section 7 does not use it.

---

## 5. What is not verified

The computations test the statements of the paper; they do not verify its
proofs. Exhaustive enumeration reaches `n = 6`, so no computation here would
detect an error that first appears at larger `n`. The window evaluation of
Theorem 7.10 verifies the arithmetic of Definition 7.7, not the lemmas that
establish `Φ⁺ ≤ Ψ(n,t)`.

The paper has not been refereed.
