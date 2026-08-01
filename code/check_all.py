#!/usr/bin/env python3
"""
check_all.py -- checks every statement of

    "Averaging in separating union-closed families of height four:
     a structural reduction"

on a corpus of separating union-closed families of height four.

Statements checked (numbering follows the paper):

  Lem 3.1   every core set omits an element of T
  Lem 3.2   the core contains no chain of three sets
  Lem 3.3   |Z \\ M| <= 1 for every maximal core set M
  Lem 3.4   M u M' is a coatom or [n] for distinct maximal M, M'
  Lem 3.5   distinct children of one M union to M; their complements in M
            are pairwise disjoint
  Lem 3.6   |A| + |A'| >= m - 1 for distinct core sets
  Prop 4.1  sum_x Ctilde_x = Phi^+                        (exact identity)
  Thm 4.2   Phi^+ <= q(t+1)                               (master inequality)
  Lem 5.1   n >= 4t+4  =>  every M has at most two children in C^+
  Thm 5.2   n >= 4t+4  =>  Phi <= 0, except Phi <= 2t+2 when q = 1
  Lem 7.1   |M| + |M'| >= n-1 for distinct maximal core sets
  Cor 7.2   at most two maximal core sets lie in C^+
  Lem 7.3   M maximal and B not inside M  =>  |B| >= n-1-|M|
  Lem 7.4   |Z \\ (A u A')| <= 1 for distinct core sets
  Prop 7.5  the Z-counting bound on Phi^+
  Thm 7.6   all of C^+ inside one maximal set  =>  the bound holds
  Prop 7.11 Ctilde_x <= (n-2) + n/t for every coatom index x
  Lem 7.13  |T\\A| + |T\\A'| >= t for distinct A, A' in C^+
  Conj 6.1  Phi^+ <= t(n-2) + n
  ground    Phi <= t(n-2) + n, i.e. Avg(A) >= n/2

Usage:  python3 check_all.py [--quick]
"""

import sys
from collections import defaultdict
from fractions import Fraction

from common import pc, invariants, default_corpus

FAILURES = defaultdict(list)


def note(tag, ok, data=None):
    if not ok:
        FAILURES[tag].append(data)


def audit(F, n):
    d = invariants(F, n)
    t, m, Tm, Zm = d["t"], d["m"], d["Tm"], d["Zm"]
    C, M, Cp, Y = d["C"], d["M"], d["Cp"], d["Y"]
    q, Phi, Phip, bound = d["q"], d["Phi"], d["Phip"], d["bound"]
    U = d["U"]

    for A in C:
        note("Lem 3.1", (Tm & ~A) != 0, (n, t, A))

    for a in C:
        for b in C:
            if b == a or (a | b) != b:
                continue
            for c in C:
                if c != b and (b | c) == c:
                    note("Lem 3.2", False, (n, t))

    for a in M:
        note("Lem 3.3", pc(Zm & ~a) <= 1, (n, t, a))

    for i, a in enumerate(M):
        for b in M[i + 1:]:
            note("Lem 3.4", (a | b) in Y or (a | b) == U, (n, t))
            cmpl = (U ^ a) & (U ^ b)
            note("Lem 3.4", pc(cmpl) <= 1 and (cmpl & Zm) == 0, (n, t))
            note("Lem 7.1", pc(a) + pc(b) >= n - 1, (n, t, pc(a), pc(b)))

    for a in M:
        kids = [N for N in C if N != a and (N | a) == a]
        for i, N in enumerate(kids):
            for N2 in kids[i + 1:]:
                note("Lem 3.5", (N | N2) == a, (n, t))
        note("Lem 3.5", sum(pc(a & ~N) for N in kids) <= pc(a), (n, t))
        for b in C:
            if (b | a) != a:
                note("Lem 7.3", pc(b) >= n - 1 - pc(a), (n, t))

    for i, a in enumerate(C):
        for b in C[i + 1:]:
            note("Lem 3.6", pc(a) + pc(b) >= m - 1, (n, t))
            note("Lem 7.4", pc(Zm & ~(a | b)) <= 1, (n, t))

    note("Cor 7.2", sum(1 for a in M if 2 * pc(a) < n) <= 2, (n, t))

    for i, a in enumerate(Cp):
        for b in Cp[i + 1:]:
            note("Lem 7.13", pc(Tm & ~a) + pc(Tm & ~b) >= t, (n, t))

    # Prop 4.1 and Prop 7.11: the fractional charge
    total = Fraction(0)
    for x in d["T"]:
        cx = Fraction(0)
        for A in Cp:
            if (A >> x) & 1:
                continue
            tau = pc(Tm & ~A)
            note("Prop 4.1 (denominator)", tau >= 1, (n, t, A))
            cx += Fraction(n - 2 * pc(A), tau)
        note("Prop 7.11", cx <= Fraction(n - 2) + Fraction(n, t), (n, t, x, float(cx)))
        total += cx
    note("Prop 4.1", total == Phip, (n, t, float(total), Phip))

    if q >= 2:
        note("Thm 4.2", Phip <= q * (t + 1), (n, t, q, Phip))

    if n >= 4 * t + 4:
        for a in M:
            kp = sum(1 for N in Cp if N != a and (N | a) == a)
            note("Lem 5.1", kp <= 2, (n, t, kp))
        note("Thm 5.2", Phi <= (2 * t + 2 if q == 1 else 0), (n, t, q, Phi))

    # Prop 7.5: the Z-counting bound
    if q >= 1:
        D = sum(pc(Zm & ~A) for A in Cp)
        note("Prop 7.5", Phip <= q * (2 * t - n) + 2 * D, (n, t, q))
        note("Prop 7.5", 4 * D * D - 4 * m * D - 4 * m * q * (q - 1) <= 0, (n, t, q))

    # Thm 7.6: all of C^+ under a single maximal set
    for a in M:
        if q >= 1 and all((b | a) == a for b in Cp):
            note("Thm 7.6", Phip <= bound, (n, t, Phip, bound))
            break

    note("Conj 6.1", Phip <= bound, (n, t, q, Phip, bound))
    note("ground truth", Phi <= bound, (n, t, Phi, bound))


def main():
    quick = "--quick" in sys.argv
    total = 0
    by_n = defaultdict(int)
    for F, n in default_corpus(quick=quick):
        audit(F, n)
        total += 1
        by_n[n] += 1
        if total % 5000 == 0:
            print(f"  ... {total} families", flush=True)

    print(f"\nfamilies audited: {total}")
    print("  by ground set size: " +
          ", ".join(f"n={k}: {v}" for k, v in sorted(by_n.items())))
    print()
    if FAILURES:
        for tag, data in sorted(FAILURES.items()):
            print(f"  FAILED {tag}: {len(data)} times, e.g. {data[0]}")
        return 1
    print("no counterexample found to any lemma, theorem or conjecture")
    return 0


if __name__ == "__main__":
    sys.exit(main())
