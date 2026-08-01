"""
common.py -- shared helpers for the verification scripts of

    "Averaging in separating union-closed families of height four:
     a structural reduction"

Sets are encoded as bitmasks over [n] = {0, ..., n-1}.
Convention: the height of a family is the maximum NUMBER OF SETS in a chain.
Pure standard library; no third-party dependencies.
"""

import itertools
import random


def pc(x):
    """Population count: the size of the set encoded by the bitmask x."""
    return bin(x).count("1")


def is_uc(F):
    """Is the family F union-closed?"""
    S = set(F)
    return all((a | b) in S for a in F for b in F)


def is_sep(F, n):
    """Is F separating on [n]?"""
    for x in range(n):
        for y in range(x + 1, n):
            if not any(((A >> x) & 1) != ((A >> y) & 1) for A in F):
                return False
    return True


def height(F):
    """Maximum number of sets in a chain of F."""
    dp, h = {}, 0
    for a in sorted(F, key=pc):
        b = 1
        for c in F:
            if c != a and (c & a) == c and c in dp:
                b = max(b, dp[c] + 1)
        dp[a] = b
        h = max(h, b)
    return h


def closure(gens, n):
    """Union-closure of the given generators, together with [n]."""
    S = set(gens)
    S.add((1 << n) - 1)
    changed = True
    while changed:
        changed = False
        for a in list(S):
            for b in list(S):
                if (a | b) not in S:
                    S.add(a | b)
                    changed = True
    return S


def qualifies(F, n):
    """Is F a separating union-closed family of height 4 with base set [n]?"""
    U = (1 << n) - 1
    if U not in F or len(F) < 2:
        return False
    u = 0
    for A in F:
        u |= A
    return u == U and is_uc(F) and is_sep(F, n) and height(F) == 4


def invariants(F, n):
    """
    Derived data used throughout the paper: the coatom index set T and its
    size t, the complement Z and m = |Z|, the core C, the maximal elements M
    of the core, the positive-weight part C^+, and q, Phi, Phi^+ and the
    bound t(n-2)+n of Conjecture 6.1.
    """
    U = (1 << n) - 1
    T = [x for x in range(n) if (U ^ (1 << x)) in F]
    t = len(T)
    Tm = sum(1 << x for x in T)
    Zm = U ^ Tm
    Y = {U ^ (1 << x) for x in T}
    C = [A for A in F if A != U and A not in Y]
    M = [a for a in C if not any(b != a and (a | b) == b for b in C)]
    Cp = [A for A in C if 2 * pc(A) < n]
    return {
        "U": U, "T": T, "t": t, "m": n - t, "Tm": Tm, "Zm": Zm,
        "Y": Y, "C": C, "M": M, "Cp": Cp, "q": len(Cp),
        "Phi": sum(n - 2 * pc(A) for A in C),
        "Phip": sum(n - 2 * pc(A) for A in Cp),
        "bound": t * (n - 2) + n,
    }


# --------------------------------------------------------------- generators

def families_exhaustive_n4():
    """Every qualifying family on [4], by brute force over all 2^16 subfamilies."""
    n, U = 4, 15
    for bits in range(1 << 16):
        F = [A for A in range(16) if (bits >> A) & 1]
        if U in F and len(F) >= 2 and qualifies(F, n):
            yield sorted(F), n


def families_closure(n, trials=None, gen_sizes=(2, 7), seed=1):
    """
    Qualifying families obtained as union-closures of generating sets.
    With trials=None every 4-element generating set is tried (used for n=5).
    """
    U = (1 << n) - 1
    pool = [A for A in range(1 << n) if A != U]
    seen = set()
    random.seed(seed)
    if trials is None:
        it = itertools.combinations(pool, 4)
    else:
        it = (tuple(random.sample(pool, random.randint(*gen_sizes)))
              for _ in range(trials))
    for g in it:
        F = frozenset(closure(list(g), n))
        if F in seen:
            continue
        seen.add(F)
        if qualifies(sorted(F), n):
            yield sorted(F), n


def families_random(n, t, trials, seed=1, size_cap=80):
    """
    Qualifying families with a prescribed coatom count, built by closing a
    random generating set that contains the t coatoms.
    """
    U = (1 << n) - 1
    random.seed(seed)
    for _ in range(trials):
        T = random.sample(range(n), t)
        gens = [U ^ (1 << x) for x in T]
        nonT = [z for z in range(n) if z not in T]
        for _ in range(random.randint(1, 6)):
            miss = set(random.sample(T, random.randint(1, t)))
            mask = sum(1 << y for y in T if y not in miss)
            if nonT:
                k = random.randint(0, max(0, n // 2))
                for z in random.sample(nonT, min(k, len(nonT))):
                    mask |= 1 << z
            gens.append(mask)
        for _ in range(random.randint(0, 3)):
            gens.append(random.getrandbits(n))
        F = closure(gens, n)
        if len(F) > size_cap:
            continue
        F = sorted(F)
        if qualifies(F, n):
            yield F, n


def default_corpus(quick=False):
    """The corpus used in the paper: exhaustive for n=4, then searches."""
    yield from families_exhaustive_n4()
    yield from families_closure(5)
    yield from families_closure(6, 20000 if quick else 200000, seed=7)
    yield from families_closure(7, 20000 if quick else 150000, seed=5)
    tmax = 5 if quick else 8
    for t in range(1, tmax + 1):
        for n in range(max(4, t + 1), min(4 * t + 8, t + 14)):
            yield from families_random(n, t, 800 if quick else 4000,
                                       seed=1000 + 13 * t + n)
