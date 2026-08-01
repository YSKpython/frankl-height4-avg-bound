[![DOI](https://zenodo.org/badge/1319205852.svg)](https://doi.org/10.5281/zenodo.21739198)

# Averaging in separating union-closed families of height four

Companion repository for the preprint
*Averaging in separating union-closed families of height four: the height-four case*
by Yavuz Selim Kılınç.

The paper is in [paper/main.tex](paper/main.tex) (compile with `pdflatex main.tex`,
twice, to resolve cross-references).

## What the paper does

Let `A ⊆ 2^[n]` be a separating union-closed family whose longest chain consists
of exactly four member sets, and let

    T = { x : [n]\{x} ∈ A },   t = |T|,   Z = [n]\T,   m = |Z| = n - t
    C⁺ = { A ∈ A : 2|A| < n },  q = |C⁺|,  Φ⁺ = Σ_{A ∈ C⁺} (n - 2|A|)

The averaged form of Frankl's conjecture asks for `Avg(A) ≥ n/2`. This is known
for height at most three, and Bouchard ([arXiv:2509.12537](https://arxiv.org/abs/2509.12537))
proved it for height four under the extra hypothesis `|B| ≤ 2`, leaving
`3 ≤ |B| ≤ 4` open. Height four is also the last height at which averaging can
work at all.

This paper proves the full height-four case, without reference to `|B|`.
By Proposition 2.1, `Avg(A) ≥ n/2` is equivalent to `Φ ≤ t(n-2)+n`, and since
`Φ ≤ Φ⁺` everything reduces to the **residual inequality** `Φ⁺ ≤ t(n-2)+n`.

### Main results

|  | statement |
| --- | --- |
| Thm 4.3 | `Φ⁺ ≤ q(t+1)` (master inequality, sharp) |
| Thm 4.4 | `(t+1)q ≤ t(n-2)+n ⇒ Avg(A) ≥ n/2` |
| Thm 5.2 | `n ≥ 4t+4 ⇒ Avg(A) ≥ n/2` (no computation) |
| Thm 6.1 | `n ≤ 10`, every `t`, and `n = 11` with `t ≤ 3` (computer-verified) |
| Thm 6.2 | **residual inequality** `Φ⁺ ≤ t(n-2)+n`, for all `n, t` |
| Thm 8.1 | **`Avg(A) ≥ n/2` for every separating union-closed family of height four** — equivalently, Frankl's conjecture holds for that class |

Sections 5 and 6 leave the window `n ≥ 11`, `t ≥ 3`, `n ≤ 4t+3`. Section 7
closes it. The mechanism is a *pair-line structure* on the small member sets:
if `A, A' ∈ C⁺` are distinct then `|S_A ∩ S_{A'}| ≥ 2 - (n mod 2)`, where
`S_A = [n]\A`, so their union is too small to escape the core and lands in the
set `M` of maximal core sets — except for a rigid disjoint pair when `n` is odd
(Lemma 7.1). This makes `C⁺` a linear space whose lines are the maximal core
sets. Bounding line capacity (Lemma 7.3, `k_M ≤ λ_M = n - |M|`), counting
complements Fisher-style (Lemmas 7.4, 7.5), and a local bound around a largest
small set (Lemma 7.6) give an explicit function `Ψ(n,t) ≥ Φ⁺` (Definition 7.7)
which is below `t(n-2)+n` throughout the window (Theorem 7.10).

The pair lemma does not use `Z`, which is why it survives where the earlier
`Z`-based counting arguments degenerate — at `t ≈ n`, i.e. exactly the hard
corner of the window.

### Why `q ≤ n-2` is not the route

Corollary 4.5 gives `Avg(A) ≥ n/2` whenever `q ≤ n-2`, and earlier drafts aimed
at proving that bound. It is false inside the window. Proposition 7.12: for even
`n`, split `[n] = M₁ ⊔ M₂` into halves and take the union closure of
`{M₁\{x} : x ∈ M₁} ∪ {M₂\{y} : y ∈ M₂}`. The result is separating,
union-closed, of height four, with `t = n` and `q = n > n-2`; for `n ≥ 12` it
satisfies every condition of the residual window. It also shows Lemma 7.5 is
sharp. So the proof bounds `Φ⁺` line by line rather than through `q`.

## Status

The proof is complete as written, machine-checked as described below, and has
**not yet been refereed**. Corrections and independent checks are welcome —
please open an issue.

## Code

Standard library only: a C compiler and Python 3, no packages.

    cd code
    make          # builds exhaust, exhaust2, verify_small
    make check    # smoke test (a few minutes)

| file | what it does |
| --- | --- |
| `verify_h4.py` | enumerates families from the definitions and checks every statement of Section 7, the value `Ψ(n,t)`, the tail inequalities and the conclusion `Avg(A) ≥ n/2` |
| `exhaust.c` | exhaustive enumeration of all qualifying families for a given `n`, pruning only with definitional constraints, checking every statement of the paper |
| `exhaust2.c` | the same enumeration with weight bookkeeping carried incrementally, for the large-`t` cases |
| `verify_small.c` | branch-and-bound verification of the residual inequality by enumerating the possible *small parts* rather than the families |
| `common.py` | shared helpers: bitmask set operations, height, closure, family generators |
| `check_all.py` | checks the lemmas of the earlier sections on a corpus of families |

## Reproducing the results

    python3 verify_h4.py                        # exact window 11..200 + tail + n=4
    python3 verify_h4.py --full --random 20000  # also n=5 exhaustive and random stress
    python3 verify_h4.py --nmax 600 --fast      # wider window, float mode
    ./exhaust 4                                 # exhaustive: 2,034 labelled families
    ./exhaust 5                                 # exhaustive: 346,028 labelled families
    ./exhaust 6 1 5                             # exhaustive for t ≤ 5: 106,040,636
    ./verify_small 8 1 8 exact                  # exact maximum of Φ⁺ for every t
    ./verify_small 10 1 10                      # residual inequality for n = 10

`exhaust` fixes the coatom index set `T` to a canonical `t`-subset, which loses
nothing because every quantity checked is invariant under permutations of `[n]`;
the counts are multiplied by `C(n,t)` to give labelled totals.

`verify_h4.py` uses exact integer upper bounds for the square-root term by
default, so the window evaluation of Theorem 7.10 involves no floating-point
arithmetic. Pass `--fast` for the float version (stress tests only).

## Computational results

Full raw output is in [RESULTS.md](RESULTS.md). Summary:

* **Exhaustive enumeration**, definitional pruning only, so the lemmas are
  tested rather than assumed: 106,388,698 labelled families over `n = 4, 5` and
  `n = 6` with `t ≤ 5`. **Zero violations of any statement.**
* **Window evaluation** of Theorem 7.10 for `11 ≤ n ≤ 200` and every `t`, in
  exact integer arithmetic: zero violations. The worst ratio
  `Ψ(n,t) / (t(n-2)+n)` is `0.723`, at `(n,t) = (11,4)`; it falls to `0.19` by
  `n = 200`. The tail argument of Theorem 7.10 covers `n ≥ 201` with room to
  spare, and each of its six inequalities is re-checked numerically to
  `n = 10,000`.
* **Small-part verification** of the residual inequality for every `n ≤ 10` and
  every `t`, and for `n = 11` with `t ≤ 3` (Theorem 6.1).
* **Extremal families**: the construction of Proposition 7.12 for
  `8 ≤ n ≤ 18` (which has `q = n > n-2` and lies inside the window), plus
  several hundred further window families built with `10 ≤ q ≤ 14`. Zero
  violations.

## Citing

@software{kilinc2026heightfour,
  author       = {K{\i}l{\i}n\c{c}, Yavuz Selim},
  title        = {Averaging in separating union-closed families of height four:
                  the height-four case},
  year         = {2026},
  publisher    = {Zenodo},
  doi          = {10.5281/zenodo.21739198},
  url          = {https://doi.org/10.5281/zenodo.21739198}
}

## Use of AI assistance

Large language models (Qwen, Alibaba Group; Claude, Anthropic) were used as a
research assistant: for exploring proof strategies, for drafting and checking
the verification code, and for language editing and LaTeX preparation. They are
not authors. See the corresponding note in the paper.

## License

MIT — see [LICENSE](LICENSE).
