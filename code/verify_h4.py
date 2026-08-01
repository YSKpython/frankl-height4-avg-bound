#!/usr/bin/env python3
"""
verify_h4.py -- machine verification for
"The pair structure of C^+ and the proof of Conjecture 6.1"

Corrected / strengthened version.

Sets are bitmasks over [n] = {0,...,n-1}.  Nothing here presupposes the new
lemmas: families are enumerated from the definitions only (union-closed,
separating, height exactly 4) and every lemma is then tested as an assertion.

Usage
-----
# Proof-oriented default:
#   exact window 11 <= n <= 200, tail check n >= 201, construction, n=4 exhaustive
python verify_h4.py

# Also n=5 exhaustive and random stress:
python verify_h4.py --full --random 20000

# Wider window stress test (fast float mode):
python verify_h4.py --nmax 600 --fast

# Wider window with exact integer upper bounds (slower):
python verify_h4.py --nmax 600
"""

import sys
import random
from math import isqrt, sqrt


# ------------------------------------------------------------------ basics --

def pc(x):
    return bin(x).count("1")


def closure(gens, n):
    F = set(gens) | {(1 << n) - 1}
    changed = True
    while changed:
        changed = False
        new = set()
        for a in F:
            for b in F:
                if (a | b) not in F:
                    new.add(a | b)
        if new:
            F |= new
            changed = True
    return F


def height(fam):
    """number of sets in a longest chain"""
    fam = sorted(fam, key=pc)
    best, h = {}, 0
    for i, s in enumerate(fam):
        b = 1
        for j in range(i):
            u = fam[j]
            if u != s and (u & s) == u and best[u] + 1 > b:
                b = best[u] + 1
        best[s] = b
        h = max(h, b)
    return h


def is_union_closed(fam):
    F = set(fam)
    return all((a | b) in F for a in F for b in F)


def is_separating(fam, n):
    for x in range(n):
        for y in range(x + 1, n):
            if not any(((s >> x) & 1) != ((s >> y) & 1) for s in fam):
                return False
    return True


def analyse(fam, n):
    full = (1 << n) - 1
    T = [x for x in range(n) if (full ^ (1 << x)) in fam]
    Tm = 0
    for x in T:
        Tm |= 1 << x
    Y = {full ^ (1 << x) for x in T}
    C = set(fam) - {full} - Y
    M = [A for A in C if not any(B != A and (A & B) == A for B in C)]
    Cp = [A for A in C if 2 * pc(A) < n]
    return dict(
        n=n,
        full=full,
        T=T,
        t=len(T),
        m=n - len(T),
        Tmask=Tm,
        Zmask=full ^ Tm,
        Y=Y,
        C=C,
        M=M,
        Cp=Cp,
        q=len(Cp),
        Phip=sum(n - 2 * pc(A) for A in Cp),
    )


# ------------------------------------------------------- global q / fmax ---

def fmax(n, t):
    """
    Upper bound for #{M in M : lambda_M = (n-1)/2}.
    """
    if n % 2 == 0 or t + 1 < (n - 1) // 2:
        return 0
    return (4 * n) // (n - 3)


def Qbound(n, t):
    """
    Largest q compatible with the global bound lemma.
    """
    m = n - t

    if n % 2 == 0:
        # q(q-1) <= t(t-1) + 2tm
        rhs = t * (t - 1) + 2 * t * m
        q = 1
        while (q + 1) * q <= rhs:
            q += 1
        return q

    # odd:
    # q^2 - 2q <= t(t-1) + 2tm + (3/2) f (n-1)
    rhs = t * (t - 1) + 2 * t * m + (3 * fmax(n, t) * (n - 1)) // 2
    q = 1
    while (q + 1) * (q + 1) - 2 * (q + 1) <= rhs:
        q += 1
    return q


# ------------------------------------------------------- fast float Psi -----

def _obj_float(r, B, w0, t):
    """
    2*min(CauchySchwarz(r), (t+1)r) - r*w0.
    Concave in r.
    """
    cs = (r + sqrt(r * r + 4.0 * r * B)) / 2.0
    return 2.0 * min(cs, (t + 1.0) * r) - r * w0


def _max_obj_float(R, B, w0, t):
    """
    Exact max over integers 1..R of the concave float objective,
    found by ternary search plus final scan.
    """
    if R <= 0:
        return -1.0e100

    lo, hi = 1, R
    while hi - lo > 2:
        m1 = lo + (hi - lo) // 3
        m2 = hi - (hi - lo) // 3
        if _obj_float(m1, B, w0, t) < _obj_float(m2, B, w0, t):
            lo = m1 + 1
        else:
            hi = m2 - 1

    return max(_obj_float(r, B, w0, t) for r in range(lo, hi + 1))


def psi_float(n, t):
    """
    Float version of Psi.  Fast, good for stress tests.
    """
    m = n - t
    R = max(1, Qbound(n, t) - 1)
    best = -1.0e100

    for w0 in range(1, min(t + 1, n) + 1):
        if (n - w0) % 2:
            continue

        a0 = (n - w0) // 2
        sig = (n + w0) // 2
        z0 = max(0, m - a0)
        B = float(sig * (sig - 1) - z0 * (z0 - 1))

        eps = 0
        if n % 2 == 1 and w0 == 1:
            eps = (n + 1) // 2 if fmax(n, t) > 0 else 1

        # r = 0 is admissible (L may be empty); the bracket is 0 there.
        Rw = max(0, R - eps)

        caseA = w0 + eps + a0 * (w0 + 2) if w0 <= 2 * t + 2 - n else -1.0e100
        caseB = w0 + eps + max(0.0, _max_obj_float(Rw, B, w0, t))
        tot = max(caseA, caseB)

        if tot > best:
            best = tot

    return best


# --------------------------------------------- exact integer Psi upper ------

def _obj_upper_int(r, B, w0, t):
    """
    Integer upper bound for
        2*min(cs(r), (t+1)r) - r*w0,
    where cs(r) = (r + sqrt(r^2 + 4Br)) / 2.

    We use ceil(sqrt(...)), hence this is a safe upper bound.
    """
    if r <= 0:
        return -10**30

    D = r * r + 4 * r * B
    s = isqrt(D)
    if s * s < D:
        s += 1

    # 2*cs <= r + s, and 2*(t+1)r is exact.
    return min(r + s, 2 * (t + 1) * r) - r * w0


def _h2_increases(r, B, c):
    """
    Exact integer test for
        h2(r+1) >= h2(r),
    where
        h2(r) = sqrt(r^2 + 4Br) - c r,
        c = w0 - 1 >= 0.

    Used to find the integer maximum of the concave second branch.
    """
    if c <= 0:
        return True

    D1 = r * r + 4 * B * r
    delta = 2 * r + 1 + 4 * B
    L = delta - c * c

    if L < 0:
        return False

    # Need L >= 2c sqrt(D1).  Both sides nonnegative, square.
    return L * L >= 4 * c * c * D1


def _h2_peak(lo, hi, B, c):
    """
    Integer maximiser of h2 on [lo, hi], assuming h2 is concave.
    """
    if lo >= hi:
        return lo

    # Find largest r in [lo, hi-1] such that h2(r+1) >= h2(r).
    l, h = lo, hi - 1
    ans = lo - 1

    while l <= h:
        mid = (l + h) // 2
        if _h2_increases(mid, B, c):
            ans = mid
            l = mid + 1
        else:
            h = mid - 1

    if ans < lo:
        return lo

    return min(ans + 1, hi)


def _max_obj_upper_int(R, B, w0, t):
    """
    Safe integer upper bound for max_{1 <= r <= R} objective.

    The objective is piecewise:
      - linear while cs >= (t+1)r;
      - h2(r) = sqrt(r^2+4Br) - (w0-1)r afterwards.

    We maximise the real objective exactly enough, then evaluate an integer
    upper bound at the relevant integer candidates.
    """
    if R <= 0:
        return -10**30

    c = w0 - 1
    denom = t * (t + 1)

    if denom <= 0 or B <= 0:
        r_cs_start = 1
    else:
        # cs(r) <= (t+1)r  iff  r >= B / (t(t+1)).
        r_cs_start = (B + denom - 1) // denom
        if r_cs_start < 1:
            r_cs_start = 1

    candidates = set()

    # Linear part: r < r_cs_start.
    lin_end = min(R, r_cs_start - 1)
    if lin_end >= 1:
        candidates.add(lin_end)

    # Second part: r >= r_cs_start.
    lo = max(1, r_cs_start)
    if lo <= R:
        candidates.add(lo)
        candidates.add(R)

        peak = _h2_peak(lo, R, B, c)
        for d in range(-5, 6):
            candidates.add(peak + d)
    else:
        candidates.add(R)

    # Boundaries, for safety.
    candidates.add(1)
    candidates.add(R)

    best = -10**30
    for r in candidates:
        if 1 <= r <= R:
            val = _obj_upper_int(r, B, w0, t)
            if val > best:
                best = val

    return best


def psi_upper_int(n, t):
    """
    Integer upper bound for Psi(n,t).  If this is <= target, the inequality
    is rigorously verified for that (n,t), up to the correctness of the
    integer arithmetic.
    """
    m = n - t
    R = max(1, Qbound(n, t) - 1)
    best = -10**30

    for w0 in range(1, min(t + 1, n) + 1):
        if (n - w0) % 2:
            continue

        a0 = (n - w0) // 2
        sig = (n + w0) // 2
        z0 = max(0, m - a0)
        B = sig * (sig - 1) - z0 * (z0 - 1)

        eps = 0
        if n % 2 == 1 and w0 == 1:
            eps = (n + 1) // 2 if fmax(n, t) > 0 else 1

        # r = 0 is admissible (L may be empty); the bracket is 0 there.
        Rw = max(0, R - eps)

        caseA = w0 + eps + a0 * (w0 + 2) if w0 <= 2 * t + 2 - n else -10**30
        caseB = w0 + eps + max(0, _max_obj_upper_int(Rw, B, w0, t))
        tot = max(caseA, caseB)

        if tot > best:
            best = tot

    if best < 0:
        return 0
    return best


# ---------------------------------------------------------------- cache -----

PSI_CACHE = {}


def psi_cached(n, t, exact=False):
    key = (n, t, exact)
    if key not in PSI_CACHE:
        PSI_CACHE[key] = psi_upper_int(n, t) if exact else psi_float(n, t)
    return PSI_CACHE[key]


# ------------------------------------------------------- window sweep -------

def window_sweep(nmax=200, verbose=True, exact=True):
    """
    Theorem (window): Psi(n,t) <= t(n-2)+n for n>=11, t>=3, n<=4t+3.

    exact=True uses integer upper bounds.
    exact=False uses fast float bounds.
    """
    fails = []
    worst = (0.0, None)

    for n in range(11, nmax + 1):
        tlo = max(3, -(-(n - 3) // 4))  # ceil((n-3)/4), but at least 3
        for t in range(tlo, n + 1):
            b = psi_cached(n, t, exact)
            tgt = t * (n - 2) + n

            if exact:
                bad = b > tgt
            else:
                bad = b > tgt + 1.0e-9

            if bad:
                fails.append((n, t, b, tgt))

            ratio = float(b) / float(tgt)
            if ratio > worst[0]:
                worst = (ratio, (n, t))

    if verbose:
        mode = "exact" if exact else "fast"
        print(f"[window]  {mode} 11 <= n <= {nmax}: violations = {len(fails)}"
              f"   worst Psi/target = {worst[0]:.3f} at (n,t) = {worst[1]}")
        for f in fails[:10]:
            print("   FAIL", f)

    return fails


def tail_check(nstop=10000, nstart=201, verbose=True):
    """
    Checks every inequality used in the tail half of Theorem (window),
    i.e. for n >= nstart = 201.  All arithmetic is exact integer arithmetic.

    (a) case B, final cubic form:  64 n^3 + 256 n^2 <= (n^2 - 11n - 16)^2
    (b) the three chain steps used to prove (a):
            11n + 16 <= n^2/16          (n >= 192)
            256 n^2  <= 2 n^3           (n >= 128)
            (225/256) n^4 >= 66 n^3     (n >= 76)
    (c) case A:  n^2 - 18n - 4 >= 0
    (d) the r = 0 branch:  w0 + eps <= (n^2 - n + 6)/4
    (e) q <= n+4 for n odd, via f <= 5
    """
    bad = 0
    for n in range(nstart, nstop + 1):
        if 64 * n**3 + 256 * n**2 > (n**2 - 11 * n - 16)**2:
            bad += 1
        if 16 * (11 * n + 16) > n**2:
            bad += 1
        if 256 * n**2 > 2 * n**3:
            bad += 1
        if 225 * n**4 < 66 * 256 * n**3:
            bad += 1
        if n**2 - 18 * n - 4 < 0:
            bad += 1
        if 4 * (3 * (n + 1)) > 2 * (n**2 - n + 6):        # r = 0 branch
            bad += 1
        if n % 2 == 1:
            if (4 * n) // (n - 3) > 5:                    # f <= 5
                bad += 1
            # (q-1)^2 <= n^2 - n + (15/2)(n-1) + 1 < (n + 13/4)^2, cleared by 16
            if 16 * (n**2 - n) + 120 * (n - 1) + 16 > (4 * n + 13)**2:
                bad += 1

    if verbose:
        print(f"[tail]    n={nstart}..{nstop}: tail inequality violations = {bad}")

    return bad


# ----------------------------------------------- per-family lemma checking --

def check_family(fam, n, exact=False):
    """
    Returns the list of violated assertions (empty = all lemmas hold).
    """
    d = analyse(fam, n)
    bad = []

    Cp = d["Cp"]
    M = d["M"]
    Y = d["Y"]
    t = d["t"]
    m = d["m"]
    q = d["q"]
    Z = d["Zmask"]

    # --- Pair lemma -------------------------------------------------------
    for i in range(len(Cp)):
        for j in range(i + 1, len(Cp)):
            A, Ap = Cp[i], Cp[j]
            U = A | Ap

            if U in M:
                continue

            ok = (
                n % 2 == 1
                and U in Y
                and 2 * pc(A) == n - 1
                and 2 * pc(Ap) == n - 1
                and (A & Ap) == 0
            )

            if not ok:
                bad.append(("pair", A, Ap))

    # --- Lines ------------------------------------------------------------
    for Mx in M:
        V = [A for A in Cp if (A & Mx) == A]
        for i in range(len(V)):
            for j in range(i + 1, len(V)):
                if (V[i] | V[j]) != Mx:
                    bad.append(("line", Mx))

    # --- Capacity ---------------------------------------------------------
    for Mx in M:
        k = sum(1 for A in Cp if (A & Mx) == A)
        lam = n - pc(Mx)
        limit = lam + 1 if (n % 2 == 1 and 2 * lam == n - 1) else lam
        if k > limit:
            bad.append(("capacity", Mx, k, lam))

    # --- Fisher-type count ------------------------------------------------
    fisher_sum = sum((n - pc(X)) * (n - pc(X) - 1) // 2 for X in M)
    fisher_bound = n * (n - 1) // 2 - m * (m - 1) // 2
    if fisher_sum > fisher_bound:
        bad.append(("fisher", fisher_sum, fisher_bound))

    # --- Global bound -----------------------------------------------------
    f_actual = sum(1 for X in M if n % 2 == 1 and 2 * (n - pc(X)) == n - 1)
    if f_actual > fmax(n, t):
        bad.append(("fmax", f_actual, fmax(n, t)))

    if q > Qbound(n, t):
        bad.append(("q>Q", q, Qbound(n, t)))

    # --- Local bound ------------------------------------------------------
    if q >= 2:
        A0 = max(Cp, key=pc)
        a0 = pc(A0)
        w0 = n - 2 * a0
        sig = n - a0
        z0 = pc(Z & ~A0)

        if w0 > t + 1:
            bad.append(("w0>t+1", w0, t + 1))

        if z0 < m - a0:
            bad.append(("z0<m-a0", z0, m - a0))

        lines = {}
        ext = []

        for A in Cp:
            if A == A0:
                continue
            U = A | A0
            if U in M:
                lines.setdefault(U, []).append(A)
            else:
                ext.append(A)

        epsb = 0
        if w0 == 1 and n % 2 == 1:
            epsb = (n + 1) // 2 if fmax(n, t) > 0 else 1

        if len(ext) > epsb:
            bad.append(("epsilon", len(ext), epsb))

        tot = w0 + sum(n - 2 * pc(A) for A in ext)

        if A0 in M:
            # Case (A)
            if any(X != A0 for X in lines):
                bad.append(("antichain",))

            if w0 > 2 * t + 2 - n:
                bad.append(("caseA-range", w0, 2 * t + 2 - n))

            s = sum(n - 2 * pc(A) for A in lines.get(A0, []))
            if s > a0 * (w0 + 2):
                bad.append(("caseA", s, a0 * (w0 + 2)))

            tot += a0 * (w0 + 2)

        else:
            # Case (B)
            if A0 in lines:
                bad.append(("caseB-A0",))

            lams = []

            for Mx, pts in lines.items():
                lam = n - pc(Mx)
                s = sum(n - 2 * pc(A) for A in pts)

                if 2 * lam > n:
                    bad.append(("caseB-big", lam))

                if lam > t + 1:
                    bad.append(("lambda>t+1", lam))

                if s > 2 * lam - w0:
                    bad.append(("caseB-line", s, 2 * lam - w0))

                tot += 2 * lam - w0
                lams.append(lam)

            B = sig * (sig - 1) - z0 * (z0 - 1)
            if sum(l * (l - 1) for l in lams) > B:
                bad.append(("caseB-fisher", sum(l * (l - 1) for l in lams), B))

            # Corrected assertion: r + epsilon <= q - 1.
            if len(lams) + len(ext) > q - 1:
                bad.append(("r+eps>q-1", len(lams), len(ext), q))

        if d["Phip"] > tot:
            bad.append(("assembled", d["Phip"], tot))

        psival = psi_cached(n, t, exact)
        if exact:
            if d["Phip"] > psival:
                bad.append(("Psi", d["Phip"], psival))
        else:
            if d["Phip"] > psival + 1.0e-9:
                bad.append(("Psi", d["Phip"], psival))

    # --- The conjecture itself --------------------------------------------
    if d["Phip"] > t * (n - 2) + n:
        bad.append(("CONJECTURE 6.1", d["Phip"], t * (n - 2) + n))

    return bad


# ----------------------------------------------------- exhaust all families --

def enumerate_h4(n, callback):
    """
    All separating union-closed families on [n] with h = 4, from definitions.

    Subsets are decided in decreasing order of size, so every union of a newly
    added set with an earlier one has already been decided.
    """
    full = (1 << n) - 1
    subs = sorted(range(full), key=lambda s: -pc(s))
    N = len(subs)

    chosen = []
    up = {full: 1}

    def rec(i):
        if i == N:
            fam = set(chosen) | {full}
            if height(fam) == 4 and is_separating(fam, n):
                callback(fam)
            return

        X = subs[i]

        # Exclude X.
        rec(i + 1)

        # Include X?
        for Yv in chosen:
            U = X | Yv
            if U != X and U != full and U not in up:
                return

        best = 1
        for Yv in up:
            if Yv != X and (X & Yv) == X and up[Yv] + 1 > best:
                best = up[Yv] + 1

        if best <= 4:
            chosen.append(X)
            up[X] = best
            rec(i + 1)
            chosen.pop()
            del up[X]

    rec(0)


def double_half(n):
    """
    The family of Proposition (q = n > n-2), n even.
    """
    assert n % 2 == 0
    full = (1 << n) - 1
    M1 = (1 << (n // 2)) - 1
    M2 = full ^ M1
    gens = [M1 ^ (1 << x) for x in range(n // 2)]
    gens += [M2 ^ (1 << y) for y in range(n // 2, n)]
    return closure(gens, n)


# ------------------------------------------------------------------- main ---

def main():
    args = sys.argv[1:]

    # Default proof window: 11 <= n <= 89.
    # The tail n >= 90 is handled by the algebraic inequality in the paper.
    nmax = 200
    if "--nmax" in args:
        nmax = int(args[args.index("--nmax") + 1])

    nrand = 0
    if "--random" in args:
        nrand = int(args[args.index("--random") + 1])

    # Default is exact integer upper bounds.
    # Use --fast for float stress tests.
    exact = "--fast" not in args

    print("=" * 70)
    print(f"# mode: {'exact integer upper bounds' if exact else 'fast float bounds'}")
    print("=" * 70)

    window_sweep(nmax, exact=exact)
    tail_check(10000)

    print("-" * 70)

    for n in (8, 10, 12, 14, 16, 18):
        F = double_half(n)
        d = analyse(F, n)
        bad = check_family(F, n, exact)
        print(
            f"[construction] n={n:2d}  UC={is_union_closed(F)} "
            f"sep={is_separating(F,n)} h={height(F)}  "
            f"t={d['t']:2d} q={d['q']:2d} (n-2={n-2:2d}) "
            f"Phi+={d['Phip']:3d} target={d['t']*(n-2)+n:4d}  "
            f"lemma violations={len(bad)}"
        )

    print("-" * 70)

    ns = [4, 5] if "--full" in args else [4]

    for n in ns:
        st = {"c": 0, "b": 0, "ex": None, "maxq": 0, "maxphi": 0}

        def cb(fam, n=n, st=st, exact=exact):
            st["c"] += 1
            d = analyse(fam, n)
            st["maxq"] = max(st["maxq"], d["q"])
            st["maxphi"] = max(st["maxphi"], d["Phip"])
            bad = check_family(fam, n, exact)
            if bad:
                st["b"] += 1
                if st["ex"] is None:
                    st["ex"] = (sorted(fam), bad)

        enumerate_h4(n, cb)

        print(
            f"[exhaustive]  n={n}: {st['c']} separating UC families with h=4 "
            f"(max q={st['maxq']}, max Phi+={st['maxphi']})  "
            f"->  lemma violations = {st['b']}"
        )

        if st["ex"]:
            print("   first counterexample:", st["ex"])

        if "--full" not in args and n == 4:
            print("   (run with --full to also enumerate n=5: 346028 families)")

    if nrand:
        print("-" * 70)
        random.seed(1)
        tot = bad = 0

        for n in range(6, 17):
            c = 0
            for _ in range(nrand):
                k = random.randint(2, 7)
                gens = []
                for _ in range(k):
                    sz = random.choice([
                        1,
                        2,
                        (n - 1) // 2,
                        n // 2 - 1,
                        n // 2,
                        n - 2,
                        random.randint(1, n - 2),
                    ])
                    sz = max(1, min(n - 2, sz))
                    gens.append(sum(1 << i for i in random.sample(range(n), sz)))

                F = closure(gens, n)
                if height(F) != 4 or not is_separating(F, n):
                    continue

                c += 1
                v = check_family(F, n, exact)
                if v:
                    bad += 1
                    print("   FAIL", n, sorted(F), v)

            tot += c
            print(f"[random] n={n:2d}: {c} families sampled")

        print(f"[random] total {tot} families, lemma violations = {bad}")

    print("=" * 70)


if __name__ == "__main__":
    main()