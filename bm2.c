/*
 * bm2.c -- the higher Bruhat order B(m,2) (rank-3 signotopes on [m], m <= 8) with single-triple
 * flips: enumeration, CSR flip graph, BFS distance distributions, dihedral symmetry, and the
 * packet-ordering test for d = |D|.
 *
 * A state is a uint64 bitmask over the C(m,3) triples in lex order; bit = 1 means sign '-'.
 * The signotope condition: for every packet a<b<c<d the bits of (abc,abd,acd,bcd) are monotone
 * (at most one change).  The 8 monotone patterns form a cycle under single flips.
 *
 * Modes:
 *   bm2 count M
 *   bm2 bfs M NSRC SEED [MAXLIST]  BFS from NSRC random orbit representatives (NSRC=0: all
 *                                  orbit representatives); prints the (d,|D|) histogram weighted
 *                                  by orbit size, and checks the packet-ordering criterion on
 *                                  every deficient target and on a sample of tight targets.
 *                                  Optional LO HI after MAXLIST restrict NSRC=0 runs to orbit
 *                                  representatives LO..HI-1 (for chunked all-pairs runs).
 *   bm2 check M < pairs            lines "tag s t" with s,t as '+'/'-' strings over lex triples;
 *                                  prints "tag |D| f forcedcyclic feasible".
 *   bm2 dump M FILE                write all states (uint64, sorted) to FILE.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXM 8
static int m, nt, np;
static int tid[MAXM][MAXM][MAXM];
static int tri[64][3];
static int pk[80][4];            /* packet -> its 4 triples abc,abd,acd,bcd */
static int tp_n[64], tp_p[64][8], tp_pos[64][8];
static int valid4[16];
static int cyc_of[16];           /* pattern -> index on the 8-cycle, -1 if invalid */
static const int cyc_pat[8] = {0, 8, 12, 14, 15, 7, 3, 1};

static void setup(int mm) {
    m = mm; nt = 0; np = 0;
    for (int a = 0; a < m; a++) for (int b = a + 1; b < m; b++) for (int c = b + 1; c < m; c++) {
        tid[a][b][c] = nt; tri[nt][0] = a; tri[nt][1] = b; tri[nt][2] = c; nt++;
    }
    memset(tp_n, 0, sizeof tp_n);
    for (int a = 0; a < m; a++) for (int b = a + 1; b < m; b++) for (int c = b + 1; c < m; c++)
        for (int d = c + 1; d < m; d++) {
            int t4[4] = {tid[a][b][c], tid[a][b][d], tid[a][c][d], tid[b][c][d]};
            for (int k = 0; k < 4; k++) {
                pk[np][k] = t4[k];
                int t = t4[k]; tp_p[t][tp_n[t]] = np; tp_pos[t][tp_n[t]] = k; tp_n[t]++;
            }
            np++;
        }
    for (int p = 0; p < 16; p++) { valid4[p] = 0; cyc_of[p] = -1; }
    for (int i = 0; i < 8; i++) { valid4[cyc_pat[i]] = 1; cyc_of[cyc_pat[i]] = i; }
}

static inline int pat(uint64_t x, int p) {
    return (int)(((x >> pk[p][0]) & 1) | (((x >> pk[p][1]) & 1) << 1) |
                 (((x >> pk[p][2]) & 1) << 2) | (((x >> pk[p][3]) & 1) << 3));
}
static inline int flippable(uint64_t x, int t) {
    for (int k = 0; k < tp_n[t]; k++) {
        int p = tp_p[t][k];
        if (!valid4[pat(x, p) ^ (1 << tp_pos[t][k])]) return 0;
    }
    return 1;
}
static int is_signotope(uint64_t x) {
    for (int p = 0; p < np; p++) if (!valid4[pat(x, p)]) return 0;
    return 1;
}

/* ---------- hash set of states ---------- */
static uint64_t *H; static int32_t *Hidx; static uint64_t Hmask;
static inline uint64_t hsh(uint64_t x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33;
    x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
static void hinit(int logcap) {
    uint64_t cap = 1ULL << logcap; Hmask = cap - 1;
    H = malloc(cap * 8); Hidx = malloc(cap * 4);
    for (uint64_t i = 0; i < cap; i++) Hidx[i] = -1;
}
static inline int64_t hfind(uint64_t x) {
    uint64_t h = hsh(x) & Hmask;
    while (Hidx[h] >= 0) { if (H[h] == x) return Hidx[h]; h = (h + 1) & Hmask; }
    return -1;
}
static inline void hput(uint64_t x, int32_t i) {
    uint64_t h = hsh(x) & Hmask;
    while (Hidx[h] >= 0) { if (H[h] == x) return; h = (h + 1) & Hmask; }
    H[h] = x; Hidx[h] = i;
}

static uint64_t *S; static int32_t NS;
static int32_t *adjst, *adj;

static int cmpu64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y;
}

static void enumerate(void) {
    int logcap = 4; while ((1 << logcap) < 4 * 1300000 && logcap < 22) logcap++;
    if (m <= 6) logcap = 12; else if (m == 7) logcap = 17; else logcap = 22;
    hinit(logcap);
    int cap = m <= 6 ? 1000 : (m == 7 ? 25000 : 1300000);
    S = malloc(sizeof(uint64_t) * cap); NS = 0;
    S[NS] = 0; hput(0, NS); NS++;
    for (int32_t q = 0; q < NS; q++) {
        uint64_t x = S[q];
        for (int t = 0; t < nt; t++) if (flippable(x, t)) {
            uint64_t y = x ^ (1ULL << t);
            if (hfind(y) < 0) { S[NS] = y; hput(y, NS); NS++; }
        }
    }
    /* sort and re-index */
    qsort(S, NS, 8, cmpu64);
    for (uint64_t i = 0; i <= Hmask; i++) Hidx[i] = -1;
    for (int32_t i = 0; i < NS; i++) hput(S[i], i);
    adjst = malloc(sizeof(int32_t) * (NS + 1));
    int64_t ne = 0;
    for (int32_t i = 0; i < NS; i++) for (int t = 0; t < nt; t++) if (flippable(S[i], t)) ne++;
    adj = malloc(sizeof(int32_t) * ne);
    ne = 0;
    for (int32_t i = 0; i < NS; i++) {
        adjst[i] = (int32_t)ne;
        for (int t = 0; t < nt; t++) if (flippable(S[i], t)) {
            int64_t j = hfind(S[i] ^ (1ULL << t));
            if (j < 0) { fprintf(stderr, "missing neighbour\n"); exit(1); }
            adj[ne++] = (int32_t)j;
        }
    }
    adjst[NS] = (int32_t)ne;
}

/* ---------- dihedral symmetry ---------- */
static int rot_idx[64], rot_neg[64], rev_idx[64];
static void setup_sym(void) {
    for (int t = 0; t < nt; t++) {
        int a = tri[t][0], b = tri[t][1], c = tri[t][2];
        /* rotation: element 0 -> m-1, i -> i-1; triples through 0 are negated */
        if (a == 0) { rot_idx[t] = tid[b - 1][c - 1][m - 1]; rot_neg[t] = 1; }
        else { rot_idx[t] = tid[a - 1][b - 1][c - 1]; rot_neg[t] = 0; }
        rev_idx[t] = tid[m - 1 - c][m - 1 - b][m - 1 - a];
    }
}
static uint64_t apply_rot(uint64_t x) {
    uint64_t y = 0;
    for (int t = 0; t < nt; t++) if ((((x >> t) & 1) ^ rot_neg[t])) y |= 1ULL << rot_idx[t];
    return y;
}
static uint64_t apply_rev(uint64_t x) {
    uint64_t y = 0;
    for (int t = 0; t < nt; t++) if ((x >> t) & 1) y |= 1ULL << rev_idx[t];
    return y;
}

/* ---------- packet-ordering criterion ---------- */
/* Build, for the pair (s,t), the forced precedence edges and the choice packets.
 * Returns 1 iff some choice of directions makes the union acyclic. */
static int K; static int loc[64];
static uint64_t forced_reach[64];
static int nch; static int ch[80][4];     /* choice packets: triples (local ids) in forward order */

static int add_edge(uint64_t *R, int u, int v) {    /* R[w] = set reachable from w */
    if ((R[v] >> u) & 1) return 0;
    if (u == v) return 0;
    uint64_t add = R[v] | (1ULL << v);
    for (int w = 0; w < K; w++) if (w == u || ((R[w] >> u) & 1)) R[w] |= add;
    return 1;
}
static int chain_ok(uint64_t *R, const int *c, int len) {
    for (int i = 0; i + 1 < len; i++) if (!add_edge(R, c[i], c[i + 1])) return 0;
    return 1;
}
static long nodes;
static int search(uint64_t *R, int i) {
    nodes++;
    if (i == nch) return 1;
    uint64_t R2[64];
    int rv[4] = {ch[i][3], ch[i][2], ch[i][1], ch[i][0]};
    memcpy(R2, R, sizeof(uint64_t) * K);
    if (chain_ok(R2, ch[i], 4) && search(R2, i + 1)) return 1;
    memcpy(R2, R, sizeof(uint64_t) * K);
    if (chain_ok(R2, rv, 4) && search(R2, i + 1)) return 1;
    return 0;
}
/* returns feasible; sets *f (choice packets) and *fc (forced graph cyclic) */
static int order_feasible(uint64_t s, uint64_t t, int *f, int *fc) {
    uint64_t Dm = s ^ t;
    K = 0;
    for (int u = 0; u < nt; u++) { loc[u] = -1; if ((Dm >> u) & 1) loc[u] = K++; }
    for (int w = 0; w < K; w++) forced_reach[w] = 0;
    nch = 0; int ok = 1;
    for (int p = 0; p < np; p++) {
        int ps = pat(s, p), pv = pat(t, p);
        int is = cyc_of[ps], iv = cyc_of[pv];
        if (is < 0 || iv < 0) { fprintf(stderr, "not a signotope\n"); exit(1); }
        int delta = (iv - is + 8) % 8;
        int len = delta <= 4 ? delta : 8 - delta;
        if (len < 2 && delta != 4) continue;
        int c[4];
        if (delta <= 4) for (int k = 0; k < delta; k++) c[k] = loc[pk[p][3 - ((is + k) % 4)]];
        else for (int k = 0; k < len; k++) c[k] = loc[pk[p][3 - ((is - 1 - k + 8) % 4)]];
        for (int k = 0; k < len; k++) if (c[k] < 0) { fprintf(stderr, "arc outside D\n"); exit(1); }
        if (delta == 4) { memcpy(ch[nch], c, sizeof c); nch++; }
        else if (ok) { if (!chain_ok(forced_reach, c, len)) ok = 0; }
    }
    *f = nch; *fc = !ok;
    if (!ok) return 0;
    nodes = 0;
    return search(forced_reach, 0);
}

static uint64_t parse(const char *str) {
    uint64_t x = 0;
    for (int i = 0; i < nt; i++) if (str[i] == '-') x |= 1ULL << i;
    return x;
}

static uint64_t rng = 88172645463325252ULL;
static uint64_t xs(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

#define BFS(dist, root) do { memset(dist, 255, NS); int qh = 0, qt = 0; dist[root] = 0; queue[qt++] = root; \
    while (qh < qt) { int32_t u = queue[qh++]; for (int32_t e = adjst[u]; e < adjst[u + 1]; e++) { int32_t w = adj[e]; \
    if (dist[w] == 255) { dist[w] = dist[u] + 1; queue[qt++] = w; } } } } while (0)

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage\n"); return 1; }
    setup(atoi(argv[2]));
    if (!strcmp(argv[1], "count")) {
        enumerate();
        int64_t ne = adjst[NS];
        int mind = 99, maxd = 0;
        for (int32_t i = 0; i < NS; i++) { int d = adjst[i + 1] - adjst[i]; if (d < mind) mind = d; if (d > maxd) maxd = d; }
        printf("m=%d |B(m,2)|=%d edges=%lld mindeg=%d maxdeg=%d\n", m, NS, (long long)ne / 2, mind, maxd);
        int bad = 0; for (int32_t i = 0; i < NS; i++) if (!is_signotope(S[i])) bad++;
        printf("non-signotopes among enumerated: %d\n", bad);
        return 0;
    }
    if (!strcmp(argv[1], "dump")) {
        enumerate();
        FILE *fo = fopen(argv[3], "wb"); fwrite(S, 8, NS, fo); fclose(fo);
        printf("wrote %d states\n", NS);
        return 0;
    }
    if (!strcmp(argv[1], "check")) {
        char tag[256], a[128], b[128];
        while (scanf("%255s %127s %127s", tag, a, b) == 3) {
            uint64_t s = parse(a), t = parse(b);
            int f, fc; int feas = order_feasible(s, t, &f, &fc);
            printf("%s %d %d %d %d %ld\n", tag, __builtin_popcountll(s ^ t), f, fc, feas, nodes);
        }
        return 0;
    }
    if (!strcmp(argv[1], "bfs")) {
        int nsrc = atoi(argv[3]); rng ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL;
        int maxlist = argc > 5 ? atoi(argv[5]) : 0;
        enumerate(); setup_sym();
        /* orbit representatives: min index in orbit */
        int32_t *orep = malloc(sizeof(int32_t) * NS); int32_t *osz = malloc(sizeof(int32_t) * NS);
        for (int32_t i = 0; i < NS; i++) orep[i] = -1;
        int32_t norb = 0; int32_t *reps = malloc(sizeof(int32_t) * NS);
        int gsize = 4 * m;
        for (int32_t i = 0; i < NS; i++) {
            if (orep[i] >= 0) continue;
            reps[norb] = i; int cnt = 0;
            uint64_t x = S[i];
            for (int r = 0; r < 2; r++) {
                uint64_t y = r ? apply_rev(x) : x;
                for (int k = 0; k < 2 * m; k++) {
                    int64_t j = hfind(y);
                    if (j < 0) { fprintf(stderr, "symmetry leaves B(m,2)\n"); return 1; }
                    if (orep[j] < 0) { orep[j] = i; cnt++; }
                    y = apply_rot(y);
                }
            }
            osz[norb] = cnt; norb++;
        }
        printf("m=%d |B|=%d orbits=%d (group order %d)\n", m, NS, norb, gsize);
        uint8_t *dist = malloc(NS); int32_t *queue = malloc(sizeof(int32_t) * NS);
        int maxdist = m * (m - 1) * (m - 2) / 6 + 1;
        int64_t (*hist)[64] = calloc(64 * 64, sizeof(int64_t));
        int64_t checked_def = 0, checked_tight = 0, mism = 0;
        int64_t fc_def = 0; int64_t fhist_def[80] = {0};
        int maxexc = 0; int ncho = 0, nex4 = 0;
        int lo = argc > 7 ? atoi(argv[6]) : 0, hi = argc > 7 ? atoi(argv[7]) : norb;
        if (hi > norb) hi = norb;
        int nrun = nsrc > 0 ? nsrc : hi - lo;
        for (int it = 0; it < nrun; it++) {
            int oi = nsrc > 0 ? (int)(xs() % norb) : lo + it;
            int32_t src = reps[oi]; int w = osz[oi];
            memset(dist, 255, NS);
            int qh = 0, qt = 0; dist[src] = 0; queue[qt++] = src;
            while (qh < qt) {
                int32_t u = queue[qh++];
                for (int32_t e = adjst[u]; e < adjst[u + 1]; e++) {
                    int32_t v = adj[e];
                    if (dist[v] == 255) { dist[v] = dist[u] + 1; queue[qt++] = v; }
                }
            }
            if (qt != NS) { fprintf(stderr, "disconnected?\n"); return 1; }
            for (int32_t j = 0; j < NS; j++) {
                int h = __builtin_popcountll(S[src] ^ S[j]); int d = dist[j];
                hist[d][h] += w;
                if (d - h > maxexc) maxexc = d - h;
                int dochk = 0;
                if (d > h) dochk = 1;
                else if ((xs() & 16383) == 0) dochk = 1;
                if (dochk && maxlist >= 0) {
                    int f, fc; int feas = order_feasible(S[src], S[j], &f, &fc);
                    if (feas != (d == h)) {
                        mism++;
                        if (mism < 10) printf("MISMATCH src=%d tgt=%d d=%d h=%d feas=%d\n", src, j, d, h, feas);
                    }
                    if (d > h && !fc && ncho < 5000) { ncho++;
                        printf("CHO %d %d d=%d h=%d f=%d ", src, j, d, h, f);
                        for (int u = 0; u < nt; u++) putchar((S[src] >> u) & 1 ? '-' : '+');
                        putchar(' ');
                        for (int u = 0; u < nt; u++) putchar((S[j] >> u) & 1 ? '-' : '+');
                        putchar('\n');
                    }
                    if (d - h >= 4 && nex4 < 3000) { nex4++;
                        printf("EXC %d %d d=%d h=%d f=%d fc=%d ", src, j, d, h, f, fc);
                        for (int u = 0; u < nt; u++) putchar((S[src] >> u) & 1 ? '-' : '+');
                        putchar(' ');
                        for (int u = 0; u < nt; u++) putchar((S[j] >> u) & 1 ? '-' : '+');
                        putchar('\n');
                    }
                    if (d > h) { checked_def++; fc_def += fc; fhist_def[f]++;
                        if (maxlist > 0 && checked_def <= maxlist) {
                            printf("DEF %d %d d=%d h=%d f=%d forcedcyc=%d ", src, j, d, h, f, fc);
                            for (int u = 0; u < nt; u++) putchar((S[src] >> u) & 1 ? '-' : '+');
                            putchar(' ');
                            for (int u = 0; u < nt; u++) putchar((S[j] >> u) & 1 ? '-' : '+');
                            putchar('\n');
                        }
                    } else checked_tight++;
                }
            }
            (void)maxdist;
        }
        printf("sources run: %d (orbit-weighted counts below are ordered pairs from these sources)\n", nrun);
        printf("hist d h count:\n");
        for (int d = 0; d < 64; d++) for (int h = 0; h < 64; h++) if (hist[d][h]) printf("H %d %d %lld\n", d, h, (long long)hist[d][h]);
        int64_t exc[64] = {0};
        for (int d = 0; d < 64; d++) for (int h = 0; h < 64; h++) if (hist[d][h]) exc[d - h] += hist[d][h];
        printf("excess distribution (orbit-weighted ordered pairs):\n");
        for (int e = 0; e < 64; e++) if (exc[e]) printf("E %d %lld\n", e, (long long)exc[e]);
        printf("max excess %d\n", maxexc);
        printf("ordering check: deficient checked %lld, tight sampled %lld, mismatches %lld\n",
               (long long)checked_def, (long long)checked_tight, (long long)mism);
        printf("deficient pairs with forced-graph cycle: %lld\n", (long long)fc_def);
        printf("choice-packet count f among deficient (unweighted):");
        for (int f = 0; f < 80; f++) if (fhist_def[f]) printf(" %d:%lld", f, (long long)fhist_def[f]);
        printf("\n");
        return 0;
    }
    if (!strcmp(argv[1], "wrong")) {
        /* For deficient pairs (s = orbit representative, v = target with d > |D|): the set of
         * triples that a shortest path flips against v (a "wrong-direction" flip, i.e. flipped away
         * from v's sign).  Each such flip costs 2.  Reports, per pair, how many wrong-direction
         * triples occur on shortest paths, split into triples outside D (doubled) and inside D
         * (tripled), and whether every doubled triple t is the unique non-D triple of some packet
         * P with |D∩P| = 3 (the long-way mechanism). */
        int maxpairs = atoi(argv[3]); rng ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL;
        enumerate(); setup_sym();
        uint8_t *ds = malloc(NS), *dv = malloc(NS); int32_t *queue = malloc(sizeof(int32_t) * NS);
        int32_t *orep = malloc(sizeof(int32_t) * NS);
        for (int32_t i = 0; i < NS; i++) orep[i] = -1;
        int32_t norb = 0; int32_t *reps = malloc(sizeof(int32_t) * NS);
        for (int32_t i = 0; i < NS; i++) {
            if (orep[i] >= 0) continue;
            reps[norb++] = i;
            for (int r = 0; r < 2; r++) { uint64_t y = r ? apply_rev(S[i]) : S[i];
                for (int k = 0; k < 2 * m; k++) { int64_t j = hfind(y); if (orep[j] < 0) orep[j] = i; y = apply_rot(y); } }
        }
        long npairs = 0, n_only_nonD = 0, n_only_D = 0, n_both = 0, n_longway_all = 0, n_longway_some = 0;
        long hist_nw[64] = {0};
        while (npairs < maxpairs) {
            int32_t src = reps[xs() % norb];
            #define BFS_UNUSED(dist, root) do { memset(dist, 255, NS); int qh = 0, qt = 0; dist[root] = 0; queue[qt++] = root; \
                while (qh < qt) { int32_t u = queue[qh++]; for (int32_t e = adjst[u]; e < adjst[u + 1]; e++) { int32_t w = adj[e]; \
                if (dist[w] == 255) { dist[w] = dist[u] + 1; queue[qt++] = w; } } } } while (0)
            BFS(ds, src);
            /* pick a random deficient target */
            int32_t tgt = -1; int tries = 0;
            while (tries++ < 200000) { int32_t j = (int32_t)(xs() % NS); if (ds[j] > __builtin_popcountll(S[src] ^ S[j])) { tgt = j; break; } }
            if (tgt < 0) continue;
            BFS(dv, tgt);
            int d = ds[tgt]; uint64_t Dm = S[src] ^ S[tgt];
            uint64_t wrong = 0;
            for (int32_t x = 0; x < NS; x++) {
                if (ds[x] + dv[x] != d) continue;
                for (int32_t e = adjst[x]; e < adjst[x + 1]; e++) {
                    int32_t y = adj[e];
                    if (ds[y] != ds[x] + 1 || dv[y] + ds[y] != d) continue;
                    uint64_t fl = S[x] ^ S[y];
                    if ((S[x] & fl) == (S[tgt] & fl)) wrong |= fl;   /* x agrees with v at t: flipped away */
                }
            }
            npairs++;
            uint64_t wn = wrong & ~Dm, wd = wrong & Dm;
            hist_nw[__builtin_popcountll(wrong)]++;
            if (wn && wd) n_both++; else if (wn) n_only_nonD++; else n_only_D++;
            int all = 1, some = 0;
            for (int t = 0; t < nt; t++) if ((wn >> t) & 1) {
                int lw = 0;
                for (int k = 0; k < tp_n[t]; k++) { int p = tp_p[t][k]; int cntD = 0;
                    for (int q = 0; q < 4; q++) cntD += (Dm >> pk[p][q]) & 1;
                    if (cntD == 3) lw = 1; }
                if (lw) some = 1; else all = 0;
            }
            if (wn) { n_longway_all += all; n_longway_some += some; }
            if (npairs <= 5) printf("pair %d %d d=%d |D|=%d wrong-direction triples: %d outside D, %d inside D\n",
                src, tgt, d, __builtin_popcountll(Dm), __builtin_popcountll(wn), __builtin_popcountll(wd));
            if (argc > 5) {   /* dump: excess, breaker mask, s, v */
                printf("BRK %d %d %llu ", d, __builtin_popcountll(Dm), (unsigned long long)wrong);
                for (int u = 0; u < nt; u++) putchar((S[src] >> u) & 1 ? '-' : '+');
                putchar(' ');
                for (int u = 0; u < nt; u++) putchar((S[tgt] >> u) & 1 ? '-' : '+');
                putchar('\n');
            }
        }
        printf("pairs %ld: wrong-direction triples only outside D %ld, only inside D %ld, both %ld\n", npairs, n_only_nonD, n_only_D, n_both);
        printf("pairs whose doubled triples all have a packet with |D∩P|=3: %ld; at least one: %ld\n", n_longway_all, n_longway_some);
        printf("number of distinct wrong-direction triples per pair:");
        for (int k = 0; k < 64; k++) if (hist_nw[k]) printf(" %d:%ld", k, hist_nw[k]);
        printf("\n");
        return 0;
    }
    if (!strcmp(argv[1], "brkall")) {
        /* All unordered deficient pairs (s,v), s < v: print "BRK d |D| mask s v" where mask is the
         * set of triples flipped against v on some shortest path (m <= 7 intended). */
        enumerate();
        uint8_t *ds = malloc(NS), *dv = malloc(NS); int32_t *queue = malloc(sizeof(int32_t) * NS);
        long np_ = 0;
        for (int32_t src = 0; src < NS; src++) {
            BFS(ds, src);
            for (int32_t tgt = src + 1; tgt < NS; tgt++) {
                if (ds[tgt] == __builtin_popcountll(S[src] ^ S[tgt])) continue;
                BFS(dv, tgt);
                int d = ds[tgt]; uint64_t wrong = 0;
                for (int32_t x = 0; x < NS; x++) {
                    if (ds[x] + dv[x] != d) continue;
                    for (int32_t e = adjst[x]; e < adjst[x + 1]; e++) {
                        int32_t y = adj[e];
                        if (ds[y] != ds[x] + 1 || dv[y] + ds[y] != d) continue;
                        uint64_t fl = S[x] ^ S[y];
                        if ((S[x] & fl) == (S[tgt] & fl)) wrong |= fl;
                    }
                }
                printf("BRK %d %d %llu ", d, __builtin_popcountll(S[src] ^ S[tgt]), (unsigned long long)wrong);
                for (int u = 0; u < nt; u++) putchar((S[src] >> u) & 1 ? '-' : '+');
                putchar(' ');
                for (int u = 0; u < nt; u++) putchar((S[tgt] >> u) & 1 ? '-' : '+');
                putchar('\n'); np_++;
            }
        }
        fprintf(stderr, "pairs %ld\n", np_);
        return 0;
    }
    fprintf(stderr, "unknown mode\n");
    return 1;
}
