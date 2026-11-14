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

# Wider window with exact full joint domain (slower):
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


# ------------------------------------------ corrected joint envelope -------

def weight_parameters(n, t, w):
    """Definition 7.7, including Nat subtraction before casting in Lean.

    Parity and 1 <= w <= t+1 <= n+1 imply w <= n, so a is nonnegative.
    z <= sigma implies B >= 0, including z=0 and z=1.
    """
    a = (n - w) // 2
    sigma = (n + w) // 2
    z = max(0, n - t - a)
    B = sigma * (sigma - 1) - z * (z - 1)
    E = 0 if n % 2 == 0 or w >= 2 else (1 if fmax(n, t) == 0 else (n + 1) // 2)
    assert a >= 0 and 0 <= z <= sigma and B >= 0
    return a, B, E


def joint_domain(q, E):
    """Exactly e <= E, rho+e+1 <= q; empty when q=0. No endpoint cut."""
    for e in range(min(E, q - 1) + 1):
        for rho in range(q - e):
            yield e, rho


def candidate_test(t, w, e, rho, B, target):
    """Exact strict test for w+e+min(linear bracket, sqrt bracket) < target.

    D>=0 is checked even when the linear branch passes. The square-root
    branch is sqrt(D) < M iff M>0 and D<M*M. Equality is never accepted.
    This also handles rho=0 without division or a special exemption.
    """
    D = rho * rho + 4 * rho * B
    linear = w + e + 2 * (t + 1) * rho - rho * w
    M = target - w - e + rho * (w - 1)
    return D >= 0 and (linear < target or (M > 0 and D < M * M))


def psi_value(n, t, exact):
    """Full joint maximum; exact=True returns a safe integer upper bound.

    This diagnostic bound uses ceil(sqrt(D)); window acceptance instead uses
    candidate_test and does not round square roots. Zero totalizes empty sets.
    """
    q = Qbound(n, t)
    best = 0
    for w in range(1, t + 2):
        if w % 2 != n % 2:
            continue
        a, B, E = weight_parameters(n, t, w)
        if w + n <= 2 * t + 2:
            best = max(best, w + E + a * (w + 2))
        for e, rho in joint_domain(q, E):
            D = rho * rho + 4 * rho * B
            root = isqrt(D) if exact else sqrt(D)
            if exact and root * root < D:
                root += 1
            bracket = min(rho + root, 2 * (t + 1) * rho) - rho * w
            best = max(best, w + e + bracket)
    return best


def psi_upper_int(n, t):
    return psi_value(n, t, True)


def psi_float(n, t):
    return psi_value(n, t, False)


# ---------------------------------------------------------------- cache -----

PSI_CACHE = {}


def psi_cached(n, t, exact=False):
    key = (n, t, exact)
    if key not in PSI_CACHE:
        PSI_CACHE[key] = psi_upper_int(n, t) if exact else psi_float(n, t)
    return PSI_CACHE[key]


# ------------------------------------------------------- window sweep -------

def window_sweep(nmax=200, verbose=True, exact=True):
    """Check EVERY corrected candidate, with independent pre-pass counts.

    No family enumeration or optimizer reduction supplies this certificate.
    --fast is diagnostic only; exact mode is mandatory for the paper result.
    """
    from time import perf_counter
    pairs = [(n, t) for n in range(11, nmax + 1) for t in range(3, n + 1)
             if n <= 4 * t + 3]
    triples = sum((t + 1 + n % 2) // 2 for n, t in pairs)
    if nmax == 200:
        assert (len(pairs), triples) == (15294, 644389)
    if verbose:
        print(f"[coverage] parameter_pairs={len(pairs)} weight_triples={triples}", flush=True)
    start = perf_counter()
    maximal = nonmaximal = 0
    fails = []
    for n, t in pairs:
        q = Qbound(n, t)
        target = t * (n - 2) + n
        assert 0 < target  # zero sentinel
        for w in range(1, t + 2):
            if w % 2 != n % 2:
                continue
            a, B, E = weight_parameters(n, t, w)
            if w + n <= 2 * t + 2:
                maximal += 1
                value = w + E + a * (w + 2)
                if value >= target:
                    fails.append(dict(kind="maximal", n=n, t=t, w=w,
                                      value=value, target=target))
            for e, rho in joint_domain(q, E):
                nonmaximal += 1
                passed = candidate_test(t, w, e, rho, B, target)
                if not exact:
                    D = rho*rho + 4*rho*B
                    passed = w+e+min(rho+sqrt(D), 2*(t+1)*rho)-rho*w < target
                if not passed:
                    D = rho*rho + 4*rho*B
                    M = target-w-e+rho*(w-1)
                    fails.append(dict(kind="nonmaximal", n=n, t=t, w=w, e=e,
                                      rho=rho, Q=q, E=E, B=B, target=target,
                                      linear=w+e+2*(t+1)*rho-rho*w,
                                      D=D, M=M, M_squared=M*M))
    if nmax == 200:
        assert (maximal, nonmaximal) == (353400, 128154974)
    if verbose:
        print(f"[window] {'exact' if exact else 'FLOAT DIAGNOSTIC'} 11..{nmax}: "
              f"maximal={maximal} nonmaximal={nonmaximal} "
              f"violations={len(fails)} seconds={perf_counter()-start:.3f}", flush=True)
        for failure in fails[:10]:
            print("   FAIL", failure)
    return fails


def tail_check(nstop=10000, nstart=201, verbose=True):
    """Exact cross-checks of the corrected analytic argument (not its proof)."""
    bad = 0
    for n in range(nstart, nstop + 1):
        # Each strict comparison used in the corrected analytic proof.
        conditions = [
            n*n-196*(n+3) == 417+(n-201)*(n+5),
            n*n > 196*(n+3),
            n*n-18*n-4 > 0,
            3*n*n-77*n-84 > 0,
            (4*n)//(n-3) <= 5,
            16*(n*n-n)+120*(n-1)+16 < (4*n+13)**2,
        ]
        bad += sum(not condition for condition in conditions)

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

    # Corrected finite window 11..200; analytic tail starts at 201.
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
    print(f"# mode: {'exact strict integer tests' if exact else 'float diagnostics only'}")
    print("=" * 70)

    if window_sweep(nmax, exact=exact) or tail_check(10000):
        raise SystemExit(1)

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

        if bad or not is_union_closed(F) or not is_separating(F, n) or height(F) != 4:
            raise AssertionError(("construction verification failed", n, sorted(F), bad))

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
            raise AssertionError(("family verification failed", st["ex"]))

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
        if bad:
            raise SystemExit(1)

    print("=" * 70)


if __name__ == "__main__":
    main()