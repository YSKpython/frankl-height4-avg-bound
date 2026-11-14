# Corrected envelope and theorem scope

Reference manuscript: `878138d49783fe2eff0c00b172cf1c0e7205510e`.
The original checkout and its three unstaged edits were preserved. They were
copied through `/tmp/manuscript-alignment-preserved.patch` to an isolated
feature worktree; the older scope recovery patch was also preserved.

## Mathematical correspondence

At the reference revision, `def:psi` is lines 1061–1117, `prop:psi` is
1133–1142, and `thm:window` is 1145–1232. Main theorem `thm:main` is
1296–1311, its introductory restatement 165–172, `thm:small` 604–613,
and the signed decomposition `prop:reform` 201–213. Labels remain stable.

The scope correction makes height exactly four and `n>=4` explicit in the
abstract, introductory/main statements, README and RESULTS. The small theorem
starts at four; the residual theorem already assumed `4<=n`, and its corollary
now retains it. Full base is the standing manuscript convention `[n]=union A`.
The n=3 family `{empty,{1},{2},{1,2},{1,2,3}}` is separating, union-closed,
height four and full base, with average 7/5<3/2; a regression verifies it.
The unchanged author thanks text remains outside `author`, as `amsart` needs.

Definition 7.7 now uses the actual joint domain

    D = {(e,rho) in Nat^2 : e<=E(n,t,w), rho+e+1<=Q(n,t)}.

The external-degree cap E is distinct from the actual degree epsilon.
The actual local theorem gives epsilon<=E and rho+epsilon+1<=q<=Q; it does
not give rho+E+1<=Q. Proposition 7.9 now proves actual-pair membership,
parameter recovery from w+2*a=n, and budget monotonicity explicitly. The
maximal eligibility filter w+n<=2*t+2 is retained. Empty classes contribute
no candidates; a zero sentinel totalizes the maximum; rho=0 has zero bracket.

Q is the largest nonnegative integer satisfying the parity-specific signed
quadratic, with f replaced by f_max in the odd branch. The manuscript states
the completed-square formula. The verifier's monotone integer scan returns the
same Q (independently checked against the formula on 4<=n<=200, 1<=t<=n).
Admissible weights are exactly 1<=w<=t+1 with matching parity. Even when t=n,
parity excludes w=n+1, so w<=n and a=(n-w)/2 is nonnegative. The definitions
of sigma, z_min, signed B, f_max and E match Lean's definitions. In particular,
z_min<=sigma implies B>=0, including z_min=0 or 1.

The analytic proof bounds every joint-domain point separately by
rho<=n+3, e<=(n+1)/2, w<=n+1, and 0<=B<=n^2. It uses
sqrt(n+3)<=n/14 for n>=201 and proves strict gaps at 201. It does not use
the former smaller range rho<=Q-1-E. The downstream residual corollary now
proves its large-n positive bound from
f=0, the parity-specific global inequalities, q<=n-2, and the master bound;
the older signed-weight theorem alone did not supply that positive bound.
The residual-to-average step is an implication via Phi<=Phi+, not an asserted
equivalence with the positive inequality. Frankl follows in particular from
averaging. The n=5 subcase in the odd capacity proof is explicitly excluded
before using strict negativity. These narrow repairs also overlap older draft
PR #1, which is preserved rather than merged wholesale. The theorem B scope
now includes n>=4 as used in its own small-q proof.

## Exact reproducibility

From `code/`:

    python3 verify_h4.py
    python3 -m unittest -v test_verify_h4
    make check

The default verifier enumerates every feasible joint pair, with no search
reduction. For target T, D=rho^2+4*rho*B, and
M=T-w-e+rho*(w-1), acceptance requires D>=0 and either the strict linear
branch comparison or M>0 and D<M^2. Because sqrt(D)>=0, the second test is
exactly the strict square-root comparison. Equality is rejected. rho=0 works
without division. Eligible maximal candidates and the zero sentinel are
checked directly. Any violation reports its tuple and integer comparisons;
the command exits nonzero. Per-family diagnostic ceil-square-root bounds and
optional floating-point diagnostics are not used for exact window acceptance.

Final exact sweep: 38.227 seconds (earlier runs took 35.781 and 43.045 seconds):

- 15,294 parameter pairs, independently formed before candidate testing;
- 644,389 parity-weight triples, counted before testing;
- 353,400 eligible maximal candidates, all passed;
- 128,154,974 nonmaximal candidates, all passed;
- analytic diagnostic checks for 201..10,000, zero violations;
- six extremal constructions and 2,034 exhaustive n=4 families, zero violations.

All counts agree with TASK-048I's independent enumeration. Historical ratios
and endpoint checks for the former envelope have been removed from current
claims. Seven standard-library regression tests pass, including command failure
propagation. `make check` passes:
C exhaustive n=4 (2,034) and n=5 (346,028), exact small-part n=8 for all t,
and a 22,266-family corpus, without violations. The Makefile's stale missing
`exhaust.c` dependency is corrected to the existing tracked `exhaust_new.c`.
Additionally, `./verify_small n 1 n` for each n=4..10 and
`./verify_small 11 1 3` verified all 52 parameter cases in 140.39 seconds.
These are verification runs with the safe remaining-weight cut, not new
exact-maxima claims. The larger n=6 historical enumeration is not rerun here.
`data/verify_log.txt` is retained as historical output from the former envelope
and 11..89 window; it is superseded by the current exact results above.
Current runtime environment: Python 3.12.14, GCC 14.2.0.

Paper build, from `paper/`:

    pdflatex -interaction=nonstopmode -halt-on-error main.tex
    pdflatex -interaction=nonstopmode -halt-on-error main.tex

Rendered pages 1–2 and 12–16 were reviewed: abstract, introductory theorem,
Definition 7.7, Proposition 7.9, Theorem 7.10, Theorem 8.1, and the Lean note.
The build produces 16 pages. Remaining pre-existing warnings are a 1.64pt
overfull line in the local proof, math in a PDF bookmark, and underfull
bibliography lines; the changed definition and formalization note fit. Generated PDF,
LaTeX outputs, Python caches and C binaries are excluded from staging.

## Audited Lean reference (read-only during this work)

[Prometheus PR #9](https://github.com/YSKpython/incognito_lab/pull/9), merged
main `8ba5fd01228e54e01c2f0001dc2041564f435ce0`; original proof source
`12bd1614b8609d1d30cf766af969491479fd81a2`.

[`Prometheus.Frankl.heightFourAveraging`](https://github.com/YSKpython/incognito_lab/blob/8ba5fd01228e54e01c2f0001dc2041564f435ce0/prometheus_v0.2/lean_proofs/Prometheus/Frankl.lean#L7196)
requires HasFullBase, IsUnionClosed, IsSeparating, posetHeight F=4, and
4<=univ.card. It proves n*F.card<=2*sum(A in F,A.card). Finite base and
nonempty F make this equivalent to average>=n/2. The merged proof's 153-entry
axiom audit allows only propext, Classical.choice and Quot.sound; the finite
certificates are kernel-checked, without Lean.ofReduceBool or trustCompiler.

Reports at that immutable commit:

- [TASK-048H: corrected joint envelope](https://github.com/YSKpython/incognito_lab/blob/8ba5fd01228e54e01c2f0001dc2041564f435ce0/prometheus_v0.2/docs/TASK_048H_CORRECTED_ENVELOPE.md)
- [TASK-048I: finite certificates and coverage](https://github.com/YSKpython/incognito_lab/blob/8ba5fd01228e54e01c2f0001dc2041564f435ce0/prometheus_v0.2/docs/TASK_048I_CORRECTED_FINITE_WINDOW.md)
- [TASK-048J: analytic tail and strict endpoint](https://github.com/YSKpython/incognito_lab/blob/8ba5fd01228e54e01c2f0001dc2041564f435ce0/prometheus_v0.2/docs/TASK_048J_ANALYTIC_WINDOW.md)
- [TASK-048P: final averaging and signed decomposition](https://github.com/YSKpython/incognito_lab/blob/8ba5fd01228e54e01c2f0001dc2041564f435ce0/prometheus_v0.2/docs/TASK_048P_HEIGHT_FOUR_AVERAGING.md)

The Python/C checks here do not themselves prove the general mathematical
statement or verify prose proofs. The separate Lean declarations supply the
formal proof in their stated scope; the paper has not been refereed.
