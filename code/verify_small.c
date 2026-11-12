/* verify_small.c -- rigorous verification of
 *
 *      Phi^+  =  sum_{A in A, 2|A| < n} (n - 2|A|)   <=   t(n-2) + n
 *
 * for EVERY separating union-closed family A on [n] of height 4 whose coatom
 * index set T has size t (T is fixed canonically; the statement is invariant
 * under relabelling).
 *
 * IDEA.  Phi^+ depends only on the member sets of size < n/2, so instead of
 * enumerating families -- hopeless once t is large -- we enumerate the possible
 * SMALL PARTS  S = {A in A : 2|A| < n}  directly.  Every family's small part
 * occurs among the states enumerated here, so a bound proved here holds for all
 * families.  A state is discarded only when it is impossible, by one of:
 *
 *  (i)   union-closedness: the closure of S under unions lies in A, and a union
 *        of size n-1 must be a coatom, i.e. must omit an element of T;
 *  (ii)  height 4: the closure contains no chain of three core sets;
 *  (iii) Lemma 3.1: every core set omits an element of T;
 *  (iv)  closure-consistency: a closure set of size < n/2 belongs to the small
 *        part, hence must itself have been selected;
 *  (v)   Lemma 3.3: a closure set properly containing another closure set is
 *        maximal in the core (else (ii) fails), so it omits at most one Z-point;
 *  (vi)  Lemma 3.6: distinct core sets A, A' satisfy |A| + |A'| >= m - 1.
 *
 * (i), (ii), (iv) are definitional.  (iii), (v), (vi) are Lemmas 3.1, 3.3, 3.6
 * of the paper; all three are proved there and were independently confirmed by
 * the exhaustive enumeration of exhaust_new.c for n <= 6.
 *
 * Two cuts are applied when verifying:
 *   - branch and bound: a subtree is skipped once the current Phi^+ plus all the
 *     remaining positive weight cannot exceed the bound (sound, since Phi^+ only
 *     increases down the tree);
 *   - Corollary 7.7: a state containing two selected sets whose union has at
 *     most (n-2)/2 elements is skipped, because the corollary already settles
 *     every family extending it.
 * Passing "exact" disables BOTH cuts and reports the true maximum of Phi^+.
 *
 * build:  gcc -O3 -o verify_small verify_small.c
 * usage:  ./verify_small <n> [tmin] [tmax] [exact]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, FULL, t, m, Tm, Zm, exact;
static int K, cand[1024], w[1024], idx_of[1 << 20];
static long long suffix[1025];
static int IN[1024], inset[1024], nin;
static long long BOUND, best, states;
static int cl[8192], ncl;

static inline int pc(int x) { return __builtin_popcount(x); }

/* Theorem 7.6 / Corollary 7.7: if two selected small sets have a union of size
   at most (n-2)/2, that union is a maximal core set and every member of C^+ is
   contained in it, so the family already satisfies the bound.  The property is
   inherited by every extension, so the whole subtree may be skipped. */
static int safe_by_thm76(void)
{
    int i, j;
    for (i = 0; i < nin; i++)
        for (j = i + 1; j < nin; j++)
            if (2 * pc(cand[IN[i]] | cand[IN[j]]) <= n - 2) return 1;
    return 0;
}

static int feasible(int upto)
{
    int i, j, k;
    ncl = 0;
    for (i = 0; i < nin; i++) cl[ncl++] = cand[IN[i]];

    for (i = 0; i < ncl; i++) {
        for (j = 0; j < ncl; j++) {
            int u = cl[i] | cl[j];
            if (u == cl[i] || u == cl[j] || u == FULL) continue;
            if (pc(u) == n - 1) {                    /* (i) */
                if (!((FULL ^ u) & Tm)) return 0;
                continue;
            }
            int found = 0;
            for (k = 0; k < ncl; k++) if (cl[k] == u) { found = 1; break; }
            if (!found) {
                if (ncl >= 8000) return 0;
                cl[ncl++] = u;
                i = -1; break;
            }
        }
    }

    for (i = 0; i < ncl; i++) {
        if (pc(cl[i]) > n - 2) continue;
        if (!(Tm & ~cl[i])) return 0;                /* (iii) */
        if (2 * pc(cl[i]) < n) {                     /* (iv) */
            int id = idx_of[cl[i]];
            if (id <= upto && !inset[id]) return 0;
        }
    }

    for (i = 0; i < ncl; i++)
        for (j = 0; j < ncl; j++) {
            if (i == j || (cl[i] | cl[j]) != cl[j] || pc(cl[j]) > n - 2) continue;
            if (pc(Zm & ~cl[j]) > 1) return 0;       /* (v) */
            for (k = 0; k < ncl; k++)                /* (ii) */
                if (k != j && (cl[j] | cl[k]) == cl[k] && pc(cl[k]) <= n - 2)
                    return 0;
        }

    for (i = 0; i < ncl; i++)                        /* (vi) */
        for (j = i + 1; j < ncl; j++)
            if (pc(cl[i]) <= n - 2 && pc(cl[j]) <= n - 2 &&
                pc(cl[i]) + pc(cl[j]) < m - 1) return 0;
    return 1;
}

static void dfs(int i, long long phip)
{
    states++;
    if (phip > best) best = phip;
    if (!exact && phip + suffix[i] <= BOUND) return;
    if (i == K) return;

    dfs(i + 1, phip);

    IN[nin++] = i; inset[i] = 1;
    if ((exact || !safe_by_thm76()) && feasible(i)) dfs(i + 1, phip + w[i]);
    nin--; inset[i] = 0;
}

static int cmpw(const void *A, const void *B)
{
    int a = *(const int *)A, b = *(const int *)B;
    if (pc(a) != pc(b)) return pc(a) - pc(b);
    return a - b;
}

int main(int argc, char **argv)
{
    n = atoi(argv[1]);
    int tmin = (argc > 2) ? atoi(argv[2]) : 1;
    int tmax = (argc > 3) ? atoi(argv[3]) : n;
    exact = (argc > 4 && !strcmp(argv[4], "exact"));
    FULL = (1 << n) - 1;

    printf("%3s %3s %7s %14s %10s %8s   %s\n", "n", "t", "cands", "states",
           "max Phi+", "bound", exact ? "status (exact max)" : "status");
    int allok = 1;
    for (t = tmin; t <= tmax; t++) {
        int x, i;
        m = n - t;
        Tm = 0;
        for (x = n - t; x < n; x++) Tm |= 1 << x;
        Zm = FULL ^ Tm;
        BOUND = (long long)t * (n - 2) + n;

        K = 0;
        for (x = 0; x <= FULL; x++) if (2 * pc(x) < n) cand[K++] = x;
        qsort(cand, K, sizeof(int), cmpw);
        for (x = 0; x <= FULL; x++) idx_of[x] = -1;
        for (i = 0; i < K; i++) { idx_of[cand[i]] = i; w[i] = n - 2 * pc(cand[i]); inset[i] = 0; }
        suffix[K] = 0;
        for (i = K - 1; i >= 0; i--) suffix[i] = suffix[i + 1] + w[i];

        best = 0; states = 0; nin = 0;
        dfs(0, 0);

        printf("%3d %3d %7d %14lld %10lld %8lld   %s\n", n, t, K, states, best,
               BOUND, best <= BOUND ? "VERIFIED" : "*** FAIL ***");
        if (best > BOUND) allok = 0;
        fflush(stdout);
    }
    return allok ? 0 : 1;
}
