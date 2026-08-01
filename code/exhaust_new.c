#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, FULL, t, m, Tm, Zm;
static int K, cand[4096], idx_of[1 << 21], isY[1 << 21];
static int *RES, *SUP, *SUPN;
static int in_[4096], inlist[4096], nin, dep[4096];
static long long n_fam, n_qual, n_viol, maxq, maxPhip;

static inline int pc(int x) { return __builtin_popcount(x); }

/* ------------------------------------------------------------ new helpers */

static int fmax_val(int nn, int tt)
{
    if (nn % 2 == 0 || tt + 1 < (nn - 1) / 2) return 0;
    return (4 * nn) / (nn - 3);
}

static long long Qbound(int nn, int tt)
{
    int mm = nn - tt;
    long long rhs, q = 1;

    if (nn % 2 == 0) {
        rhs = (long long)tt * (tt - 1) + 2LL * tt * mm;
        while ((q + 1) * q <= rhs) q++;
        return q;
    }

    rhs = (long long)tt * (tt - 1) + 2LL * tt * mm
        + (3LL * fmax_val(nn, tt) * (nn - 1)) / 2;
    while ((q + 1) * (q + 1) - 2 * (q + 1) <= rhs) q++;
    return q;
}

static int in_Mx(int U, int *Mx, int nm)
{
    int i;
    for (i = 0; i < nm; i++) if (Mx[i] == U) return 1;
    return 0;
}

/* ---------------------------------------------------------------- checks */

static void examine(void)
{
    int C[4096], nc = 0, Cp[4096], ncp = 0;
    int Mx[4096], nm = 0;
    int i, j, k;
    int bad = 0;

    for (i = 0; i < nin; i++) C[nc++] = cand[inlist[i]];

    for (i = 0; i < nc; i++) {
        int maximal = 1;
        for (j = 0; j < nc; j++)
            if (j != i && (C[i] | C[j]) == C[j]) { maximal = 0; break; }
        if (maximal) Mx[nm++] = C[i];
    }

    /* ---------------- old structural checks from the first paper --------- */

    for (i = 0; i < nc; i++)                                   /* L3.1 */
        if ((Tm & ~C[i]) == 0) { printf("  VIOLATION L3.1 t=%d\n", t); bad = 1; }

    for (i = 0; i < nc; i++)                                   /* L3.2 */
        for (j = 0; j < nc; j++) {
            if (j == i || (C[i] | C[j]) != C[j]) continue;
            for (k = 0; k < nc; k++)
                if (k != j && (C[j] | C[k]) == C[k])
                    { printf("  VIOLATION L3.2 t=%d\n", t); bad = 1; }
        }

    for (i = 0; i < nm; i++)                                   /* L3.3 */
        if (pc(Zm & ~Mx[i]) > 1) { printf("  VIOLATION L3.3 t=%d\n", t); bad = 1; }

    for (i = 0; i < nm; i++)                                   /* L3.4 */
        for (j = i + 1; j < nm; j++) {
            int u = Mx[i] | Mx[j];
            int cmp = (FULL ^ Mx[i]) & (FULL ^ Mx[j]);
            if (u != FULL && !isY[u]) { printf("  VIOLATION L3.4a t=%d\n", t); bad = 1; }
            if (pc(cmp) > 1 || (cmp & Zm)) { printf("  VIOLATION L3.4b t=%d\n", t); bad = 1; }
        }

    for (i = 0; i < nm; i++) {                                 /* L3.5 */
        int sum = 0;
        for (j = 0; j < nc; j++) {
            if (C[j] == Mx[i] || (C[j] | Mx[i]) != Mx[i]) continue;
            sum += pc(Mx[i] & ~C[j]);
            for (k = 0; k < nc; k++) {
                if (k == j || C[k] == Mx[i] || (C[k] | Mx[i]) != Mx[i]) continue;
                if ((C[j] | C[k]) != Mx[i]) { printf("  VIOLATION L3.5a t=%d\n", t); bad = 1; }
            }
        }
        if (sum > pc(Mx[i])) { printf("  VIOLATION L3.5b t=%d\n", t); bad = 1; }
    }

    for (i = 0; i < nc; i++)                                   /* L3.6 */
        for (j = i + 1; j < nc; j++)
            if (pc(C[i]) + pc(C[j]) < m - 1)
                { printf("  VIOLATION L3.6 t=%d\n", t); bad = 1; }

    /* Build C^+ and Phi / Phi^+. */
    long long Phi = 0, Phip = 0, q = 0, charge = 0;
    for (i = 0; i < nc; i++) {
        int w = n - 2 * pc(C[i]);
        Phi += w;
        if (w > 0) {
            Cp[ncp++] = C[i];
            Phip += w;
            q++;
            if (pc(Tm & ~C[i]) == 0) { printf("  VIOLATION P4.1 denom t=%d\n", t); bad = 1; }
            else charge += w;                                  /* P4.1 */
        }
    }
    if (charge != Phip) { printf("  VIOLATION P4.1 t=%d\n", t); bad = 1; }

    if (q >= 2 && Phip > q * (long long)(t + 1))               /* T4.2 */
        { printf("  VIOLATION T4.2 t=%d q=%lld Phi+=%lld\n", t, q, Phip); bad = 1; }

    if (n >= 4 * t + 4) {
        for (i = 0; i < nm; i++) {                             /* L5.1 */
            int kp = 0;
            for (j = 0; j < nc; j++)
                if (C[j] != Mx[i] && (C[j] | Mx[i]) == Mx[i] && 2 * pc(C[j]) < n) kp++;
            if (kp > 2) { printf("  VIOLATION L5.1 t=%d k=%d\n", t, kp); bad = 1; }
        }
        long long lim = (q == 1) ? (2LL * t + 2) : 0;          /* T5.2 */
        if (Phi > lim) { printf("  VIOLATION T5.2 t=%d q=%lld Phi=%lld\n", t, q, Phi); bad = 1; }
    }

    /* ----------------------- new closing-section assertions -------------- */

    /* Pair lemma. */
    for (i = 0; i < ncp; i++) {
        for (j = i + 1; j < ncp; j++) {
            int U = Cp[i] | Cp[j];
            if (in_Mx(U, Mx, nm)) continue;
            int ok = (n % 2 == 1) && isY[U]
                     && (2 * pc(Cp[i]) == n - 1)
                     && (2 * pc(Cp[j]) == n - 1)
                     && ((Cp[i] & Cp[j]) == 0);
            if (!ok) {
                printf("  VIOLATION PAIR t=%d\n", t);
                bad = 1;
            }
        }
    }

    /* Lines + capacity. */
    for (i = 0; i < nm; i++) {
        int V[4096], nv = 0;
        for (j = 0; j < ncp; j++)
            if ((Cp[j] | Mx[i]) == Mx[i]) V[nv++] = Cp[j];

        for (j = 0; j < nv; j++)
            for (k = j + 1; k < nv; k++)
                if ((V[j] | V[k]) != Mx[i]) {
                    printf("  VIOLATION LINES t=%d\n", t);
                    bad = 1;
                }

        int lam = n - pc(Mx[i]);
        int limit = lam + ((n % 2 == 1 && 2 * lam == n - 1) ? 1 : 0);
        if (nv > limit) {
            printf("  VIOLATION CAPACITY t=%d k=%d lam=%d limit=%d\n", t, nv, lam, limit);
            bad = 1;
        }
    }

    /* Fisher-type count. */
    {
        long long fisher_sum = 0;
        for (i = 0; i < nm; i++) {
            long long lam = n - pc(Mx[i]);
            fisher_sum += lam * (lam - 1) / 2;
        }
        long long fisher_bound = (long long)n * (n - 1) / 2 - (long long)m * (m - 1) / 2;
        if (fisher_sum > fisher_bound) {
            printf("  VIOLATION FISHER t=%d sum=%lld bound=%lld\n", t, fisher_sum, fisher_bound);
            bad = 1;
        }
    }

    /* Global bound: f and q. */
    {
        int f_actual = 0;
        for (i = 0; i < nm; i++) {
            int lam = n - pc(Mx[i]);
            if (n % 2 == 1 && 2 * lam == n - 1) f_actual++;
        }
        int fm = fmax_val(n, t);
        if (f_actual > fm) {
            printf("  VIOLATION FMAX t=%d f=%d fmax=%d\n", t, f_actual, fm);
            bad = 1;
        }

        long long Qb = Qbound(n, t);
        if (q > Qb) {
            printf("  VIOLATION QBOUND t=%d q=%lld Q=%lld\n", t, q, Qb);
            bad = 1;
        }
    }

    /* Local bound around a largest member of C^+. */
    if (q >= 2) {
        int A0 = Cp[0];
        for (i = 1; i < ncp; i++)
            if (pc(Cp[i]) > pc(A0)) A0 = Cp[i];

        int a0 = pc(A0);
        int w0 = n - 2 * a0;
        int sig = n - a0;
        int z0 = pc(Zm & ~A0);

        if (w0 > t + 1) {
            printf("  VIOLATION LOCAL w0>t+1 t=%d w0=%d\n", t, w0);
            bad = 1;
        }
        if (z0 < m - a0) {
            printf("  VIOLATION LOCAL z0<m-a0 t=%d z0=%d\n", t, z0);
            bad = 1;
        }

        int A0_in_M = 0;
        for (i = 0; i < nm; i++) if (Mx[i] == A0) A0_in_M = 1;

        int fm = fmax_val(n, t);
        int epsb = 0;
        if (w0 == 1 && (n % 2 == 1))
            epsb = (fm > 0) ? ((n + 1) / 2) : 1;

        long long ext = 0, ext_weight = 0, child_sum = 0;
        for (i = 0; i < ncp; i++) {
            if (Cp[i] == A0) continue;
            int U = Cp[i] | A0;
            if (in_Mx(U, Mx, nm)) {
                if (A0_in_M && U != A0) {
                    printf("  VIOLATION LOCAL antichain t=%d\n", t);
                    bad = 1;
                }
                if (U == A0) child_sum += n - 2 * pc(Cp[i]);
            } else {
                ext++;
                ext_weight += n - 2 * pc(Cp[i]);
            }
        }

        if (ext > epsb) {
            printf("  VIOLATION LOCAL epsilon t=%d ext=%lld eps=%d\n", t, ext, epsb);
            bad = 1;
        }
        if (ext_weight != ext) {
            printf("  VIOLATION LOCAL ext_weight t=%d ext_weight=%lld ext=%lld\n", t, ext_weight, ext);
            bad = 1;
        }

        long long tot = w0 + ext_weight;

        if (A0_in_M) {
            if (w0 > 2 * t + 2 - n) {
                printf("  VIOLATION LOCAL caseA-range t=%d w0=%d\n", t, w0);
                bad = 1;
            }
            if (child_sum > (long long)a0 * (w0 + 2)) {
                printf("  VIOLATION LOCAL caseA t=%d child_sum=%lld bound=%lld\n",
                       t, child_sum, (long long)a0 * (w0 + 2));
                bad = 1;
            }
            tot += (long long)a0 * (w0 + 2);
        } else {
            long long local_fisher = 0;
            long long r = 0;

            for (i = 0; i < nm; i++) {
                if ((A0 | Mx[i]) != Mx[i]) continue;

                long long s = 0;
                int has = 0;
                for (j = 0; j < ncp; j++) {
                    if (Cp[j] == A0) continue;
                    if ((Cp[j] | Mx[i]) == Mx[i]) {
                        s += n - 2 * pc(Cp[j]);
                        has = 1;
                    }
                }
                if (!has) continue;

                r++;
                int lam = n - pc(Mx[i]);

                if (2 * lam > n) {
                    printf("  VIOLATION LOCAL caseB-big t=%d lam=%d\n", t, lam);
                    bad = 1;
                }
                if (lam > t + 1) {
                    printf("  VIOLATION LOCAL lambda>t+1 t=%d lam=%d\n", t, lam);
                    bad = 1;
                }
                if (s > 2 * lam - w0) {
                    printf("  VIOLATION LOCAL caseB-line t=%d s=%lld bound=%d\n",
                           t, s, 2 * lam - w0);
                    bad = 1;
                }

                tot += 2 * lam - w0;
                local_fisher += (long long)lam * (lam - 1);
            }

            long long B = (long long)sig * (sig - 1) - (long long)z0 * (z0 - 1);
            if (local_fisher > B) {
                printf("  VIOLATION LOCAL caseB-fisher t=%d sum=%lld B=%lld\n",
                       t, local_fisher, B);
                bad = 1;
            }
            if (r + ext > q - 1) {
                printf("  VIOLATION LOCAL r+eps>q-1 t=%d r=%lld ext=%lld q=%lld\n",
                       t, r, ext, q);
                bad = 1;
            }
        }

        if (Phip > tot) {
            printf("  VIOLATION LOCAL assembled t=%d Phip=%lld tot=%lld\n", t, Phip, tot);
            bad = 1;
        }
    }

    /* The now-proved residual inequality and the averaging ground truth. */
    if (Phip > (long long)t * (n - 2) + n)                     /* residual inequality */
        { printf("  VIOLATION RESIDUAL t=%d q=%lld Phi+=%lld\n", t, q, Phip); bad = 1; }

    if (Phi > (long long)t * (n - 2) + n)                      /* Avg >= n/2 */
        { printf("  VIOLATION GROUND TRUTH t=%d Phi=%lld\n", t, Phi); bad = 1; }

    if (bad) n_viol++;
    if (q > maxq) maxq = q;
    if (Phip > maxPhip) maxPhip = Phip;
    n_qual++;
}

/* ------------------------------------------------------------------ DFS */

static void leaf(void)
{
    int i, z, y;
    n_fam++;

    for (i = 0; i < nin; i++) if (dep[inlist[i]] == 4) goto has4;
    return;

has4:
    for (z = 0; z < n; z++) {
        if (!((Zm >> z) & 1)) continue;
        for (y = z + 1; y < n; y++) {
            if (!((Zm >> y) & 1)) continue;
            for (i = 0; i < nin; i++) {
                int A = cand[inlist[i]];
                if (((A >> z) & 1) != ((A >> y) & 1)) goto sep;
            }
            return;
sep:
            ;
        }
    }
    examine();
}

static void dfs(int i)
{
    if (i == K) { leaf(); return; }

    in_[i] = 0;
    dfs(i + 1);

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

    dep[i] = d;
    in_[i] = 1;
    inlist[nin++] = i;
    dfs(i + 1);
    nin--;
    in_[i] = 0;
}

/* ----------------------------------------------------------------- main */

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
    n = atoi(argv[1]);
    int tmin = (argc > 2) ? atoi(argv[2]) : 0;
    int tmax = (argc > 3) ? atoi(argv[3]) : n;
    FULL = (1 << n) - 1;

    long long g_qual = 0, g_lab = 0, g_viol = 0;

    printf("%3s %3s %14s %13s %6s %9s %7s %14s\n",
           "n", "t", "UC-families", "qualifying", "max q", "max Phi+", "bound", "labelled");

    for (t = tmin; t <= tmax; t++) {
        int x, i, j;
        m = n - t;
        Tm = 0;
        for (x = n - t; x < n; x++) Tm |= 1 << x;
        Zm = FULL ^ Tm;

        for (x = 0; x <= FULL; x++) { isY[x] = 0; idx_of[x] = -1; }
        for (x = 0; x < n; x++) if ((Tm >> x) & 1) isY[FULL ^ (1 << x)] = 1;

        K = 0;
        for (x = 0; x <= FULL; x++) if (pc(x) <= n - 2) cand[K++] = x;
        qsort(cand, K, sizeof(int), cmpsz);
        for (i = 0; i < K; i++) idx_of[cand[i]] = i;

        RES = malloc(sizeof(int) * (size_t)K * K);
        SUP = malloc(sizeof(int) * (size_t)K * K);
        SUPN = malloc(sizeof(int) * K);

        for (i = 0; i < K; i++) {
            SUPN[i] = 0;
            for (j = 0; j < K; j++) {
                int u = cand[i] | cand[j];
                if (u == cand[i] || u == cand[j] || u == FULL || isY[u])
                    RES[(size_t)i * K + j] = -1;
                else if (pc(u) > n - 2) RES[(size_t)i * K + j] = -2;
                else RES[(size_t)i * K + j] = idx_of[u];

                if (j != i && (cand[i] | cand[j]) == cand[j])
                    SUP[(size_t)i * K + SUPN[i]++] = j;
            }
        }

        n_fam = n_qual = n_viol = 0; maxq = 0; maxPhip = -1000000; nin = 0;
        memset(in_, 0, sizeof(int) * K);
        dfs(0);

        long long lab = n_qual * binom(n, t);
        printf("%3d %3d %14lld %13lld %6lld %9lld %7lld %14lld%s\n",
               n, t, n_fam, n_qual, maxq, maxPhip,
               (long long)t * (n - 2) + n, lab,
               n_viol ? "   *** VIOLATIONS ***" : "");
        fflush(stdout);

        g_qual += n_qual; g_lab += lab; g_viol += n_viol;
        free(RES); free(SUP); free(SUPN);
    }

    printf("\ncanonical-T families: %lld   labelled families: %lld   violations: %lld\n",
           g_qual, g_lab, g_viol);

    return g_viol ? 1 : 0;
}
