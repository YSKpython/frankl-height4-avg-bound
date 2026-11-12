/* exhaust2.c -- same exhaustive enumeration as exhaust_new.c, with the weight
 * bookkeeping carried incrementally through the DFS so that the per-family
 * cost is O(1).  Intended for the large-t cases (n = 6, t = 6 and n = 7).
 *
 * Pruning uses only definitional constraints (core sets of size <= n-2,
 * union-closedness, no chain of five member sets).  Verified quantities:
 *
 *   C6.1   Phi^+ <= t(n-2) + n            (the conjecture)
 *   GT     Phi   <= t(n-2) + n            (equivalent to Avg >= n/2)
 *   T4.2   Phi^+ <= q(t+1)   for q >= 2   (master inequality)
 *   T5.2   n >= 4t+4  =>  Phi <= 0  (or <= 2t+2 when q = 1)
 *
 * The remaining lemmas are structural and were checked in full by exhaust_new.c
 * for n <= 5 (all t) and n = 6 (t <= 5); FULLCHK below re-runs them on a
 * sample of the families here as an extra guard.
 *
 * build:  gcc -O3 -march=native -o exhaust2 exhaust2.c
 * usage:  ./exhaust2 <n> <t> [sample]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 u128;

static int n, FULL, t, m, Tm, Zm;
static int K, cand[4096], idx_of[1 << 21], isY[1 << 21];
static int *RES, *SUP, *SUPN;
static int in_[4096], inlist[4096], nin, dep[4096];
static int wgt[4096];
static u128 sig[32];

static long long n_fam, n_qual, n_viol, maxq, maxPhip, sample, seen;
static long long Phi, Phip, q, cnt4;
static long long BOUND;

static inline int pc(int x) { return __builtin_popcount(x); }

/* ---- full structural re-check on sampled families ---------------------- */
static void fullcheck(void)
{
    int C[4096], nc = 0, i, j, k;
    for (i = 0; i < nin; i++) C[nc++] = cand[inlist[i]];
    int Mx[4096], nm = 0;
    for (i = 0; i < nc; i++) {
        int mx = 1;
        for (j = 0; j < nc; j++)
            if (j != i && (C[i] | C[j]) == C[j]) { mx = 0; break; }
        if (mx) Mx[nm++] = C[i];
    }
    for (i = 0; i < nc; i++)
        if ((Tm & ~C[i]) == 0) { printf("  VIOLATION L3.1\n"); n_viol++; }
    for (i = 0; i < nm; i++)
        if (pc(Zm & ~Mx[i]) > 1) { printf("  VIOLATION L3.3\n"); n_viol++; }
    for (i = 0; i < nm; i++)
        for (j = i + 1; j < nm; j++) {
            int u = Mx[i] | Mx[j], cmp = (FULL ^ Mx[i]) & (FULL ^ Mx[j]);
            if (u != FULL && !isY[u]) { printf("  VIOLATION L3.4a\n"); n_viol++; }
            if (pc(cmp) > 1 || (cmp & Zm)) { printf("  VIOLATION L3.4b\n"); n_viol++; }
        }
    for (i = 0; i < nm; i++) {
        int sum = 0;
        for (j = 0; j < nc; j++) {
            if (C[j] == Mx[i] || (C[j] | Mx[i]) != Mx[i]) continue;
            sum += pc(Mx[i] & ~C[j]);
            for (k = 0; k < nc; k++) {
                if (k == j || C[k] == Mx[i] || (C[k] | Mx[i]) != Mx[i]) continue;
                if ((C[j] | C[k]) != Mx[i]) { printf("  VIOLATION L3.5a\n"); n_viol++; }
            }
        }
        if (sum > pc(Mx[i])) { printf("  VIOLATION L3.5b\n"); n_viol++; }
    }
    for (i = 0; i < nc; i++)
        for (j = i + 1; j < nc; j++)
            if (pc(C[i]) + pc(C[j]) < m - 1) { printf("  VIOLATION L3.6\n"); n_viol++; }
    if (n >= 4 * t + 4)
        for (i = 0; i < nm; i++) {
            int kp = 0;
            for (j = 0; j < nc; j++)
                if (C[j] != Mx[i] && (C[j] | Mx[i]) == Mx[i] && 2 * pc(C[j]) < n) kp++;
            if (kp > 2) { printf("  VIOLATION L5.1 k=%d\n", kp); n_viol++; }
        }
}

/* ---- leaf --------------------------------------------------------------- */
static void leaf(void)
{
    n_fam++;
    if (!cnt4) return;                         /* height must be exactly 4 */
    int z, y;
    for (z = 0; z < n; z++) {                  /* separating: Z-pairs only */
        if (!((Zm >> z) & 1)) continue;
        for (y = z + 1; y < n; y++) {
            if (!((Zm >> y) & 1)) continue;
            if (sig[z] == sig[y]) return;
        }
    }
    n_qual++;
    if (Phip > BOUND) { printf("  VIOLATION C6.1 q=%lld Phi+=%lld\n", q, Phip); n_viol++; }
    if (Phi > BOUND)  { printf("  VIOLATION GROUND TRUTH Phi=%lld\n", Phi); n_viol++; }
    if (q >= 2 && Phip > q * (t + 1)) { printf("  VIOLATION T4.2 q=%lld\n", q); n_viol++; }
    if (n >= 4 * t + 4) {
        long long lim = (q == 1) ? (2LL * t + 2) : 0;
        if (Phi > lim) { printf("  VIOLATION T5.2 q=%lld Phi=%lld\n", q, Phi); n_viol++; }
    }
    if (q > maxq) maxq = q;
    if (Phip > maxPhip) maxPhip = Phip;
    if (sample && ++seen % sample == 0) fullcheck();
}

static void dfs(int i)
{
    if (i == K) { leaf(); return; }
    dfs(i + 1);                                 /* exclude */

    int j;
    for (j = 0; j < nin; j++) {
        int r = RES[(size_t)i * K + inlist[j]];
        if (r == -1) continue;
        if (r == -2 || !in_[r]) return;
    }
    int d = (Tm & ~cand[i]) ? 3 : 2;
    for (j = 0; j < SUPN[i]; j++) {
        int s = SUP[(size_t)i * K + j];
        if (in_[s] && dep[s] + 1 > d) d = dep[s] + 1;
    }
    if (d > 4) return;

    int w = wgt[i];
    dep[i] = d; in_[i] = 1; inlist[nin++] = i;
    Phi += w; if (w > 0) { Phip += w; q++; }
    if (d == 4) cnt4++;
    u128 bit = (u128)1 << (nin - 1);
    for (j = 0; j < n; j++) if ((cand[i] >> j) & 1) sig[j] |= bit;

    dfs(i + 1);

    for (j = 0; j < n; j++) if ((cand[i] >> j) & 1) sig[j] &= ~bit;
    if (d == 4) cnt4--;
    Phi -= w; if (w > 0) { Phip -= w; q--; }
    nin--; in_[i] = 0;
}

static long long binom(int a, int b)
{
    long long r = 1; int i;
    if (b > a - b) b = a - b;
    for (i = 0; i < b; i++) r = r * (a - i) / (i + 1);
    return r;
}
static int cmpsz(const void *A, const void *B)
{
    int a = *(const int *)A, b = *(const int *)B;
    if (pc(a) != pc(b)) return pc(b) - pc(a);
    return a - b;
}

int main(int argc, char **argv)
{
    n = atoi(argv[1]); t = atoi(argv[2]);
    sample = (argc > 3) ? atoll(argv[3]) : 0;
    FULL = (1 << n) - 1; m = n - t;
    BOUND = (long long)t * (n - 2) + n;

    int x, i, j;
    Tm = 0;
    for (x = n - t; x < n; x++) Tm |= 1 << x;
    Zm = FULL ^ Tm;
    for (x = 0; x <= FULL; x++) { isY[x] = 0; idx_of[x] = -1; }
    for (x = 0; x < n; x++) if ((Tm >> x) & 1) isY[FULL ^ (1 << x)] = 1;

    K = 0;
    for (x = 0; x <= FULL; x++) if (pc(x) <= n - 2) cand[K++] = x;
    qsort(cand, K, sizeof(int), cmpsz);
    for (i = 0; i < K; i++) { idx_of[cand[i]] = i; wgt[i] = n - 2 * pc(cand[i]); }

    RES = malloc(sizeof(int) * (size_t)K * K);
    SUP = malloc(sizeof(int) * (size_t)K * K);
    SUPN = malloc(sizeof(int) * K);
    for (i = 0; i < K; i++) {
        SUPN[i] = 0;
        for (j = 0; j < K; j++) {
            int u = cand[i] | cand[j];
            if (u == cand[i] || u == cand[j] || u == FULL || isY[u]) RES[(size_t)i * K + j] = -1;
            else if (pc(u) > n - 2) RES[(size_t)i * K + j] = -2;
            else RES[(size_t)i * K + j] = idx_of[u];
            if (j != i && (cand[i] | cand[j]) == cand[j]) SUP[(size_t)i * K + SUPN[i]++] = j;
        }
    }
    memset(sig, 0, sizeof(sig));
    dfs(0);

    printf("n=%d t=%d  UC-families=%lld  qualifying=%lld  max q=%lld  "
           "max Phi+=%lld  bound=%lld  labelled=%lld  violations=%lld\n",
           n, t, n_fam, n_qual, maxq, maxPhip, BOUND,
           n_qual * binom(n, t), n_viol);
    return n_viol ? 1 : 0;
}
