/* (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
 *
 * gridcert.c -- plan-cert32 milestone M2, ENGINE B:
 *               the cell subshift of finite type on [0,1), its forward core,
 *               and the zero-entropy certificate.  Handles arbitrary finite
 *               unions U of rational intervals (plan §4.2).
 *
 * MODEL (plan §1.1).  With x_n = [xi (3/2)^n], y_n = {xi (3/2)^n}:
 *
 *     y_{n+1} = (3 y_n + e_n)/2,   e_n = 3 x_n - 2 x_{n+1} in {-2,-1,0,1}.
 *
 * Partition [0,1) into N cells [i/N,(i+1)/N).  States = cells meeting U; there
 * is an edge i --e--> j iff the image of cell i under y |-> (3y+e)/2 meets cell
 * j (exact integer arithmetic over the denominator 2N), and cell j meets U.
 *
 * SOUNDNESS (one-sided, the only lemma the certificates need): a real orbit
 * confined to U traces an infinite admissible path.  Cell granularity can only
 * ADD spurious paths, never fake a kill.
 *
 * TWO CERTIFICATES, in increasing strength of what they need:
 *
 *   (C1) EMPTY CORE.  Peel states with no live successor to a fixpoint.  Empty
 *        core => no infinite path => Z(U) = empty, unconditionally.  (And
 *        Z_ev(U) = empty by the shift trick, FLP/Capstone.lean.)
 *
 *   (C2) ZERO ENTROPY.  Core nonempty but no strongly connected component of
 *        the core is branching (every cyclic SCC is a simple cycle).  Then every
 *        infinite path is eventually periodic -- the condensation is a finite
 *        DAG, so a path ends up inside one SCC, and a simple cycle leaves it no
 *        choice.  Distinct carries e give target cells N/2 apart, so the label
 *        sequence is read off the vertex path: the carry word of any confined
 *        orbit would be eventually periodic.  It is not, for ANY xi != 0:
 *        Z32.not_isEventuallyPeriodic_carry (= [DN05] Lemma 2, PROVED in the
 *        corpus, std3).  Hence Z(U) = empty.
 *        This is DubC's C(P) certificate transplanted to the fractional side,
 *        and it is what lets the engine certify the FLP positions, where the
 *        core is a nonempty finite cycle.
 *
 * Anything else is the undecided BAND: reported with core size, number of
 * branching SCCs and the growth rate lambda (T5 dimension data,
 * dim_box <= log lambda / log(3/2)).
 *
 * Build:  gcc -O2 -o gridcert gridcert.c -lm
 * Modes:
 *   ./gridcert cert <N> <Gden> <lo1> <hi1> [<lo2> <hi2> ...]
 *        U = union of closed [lo_t/Gden, hi_t/Gden] at resolution N.
 *   ./gridcert ladder <N0> <mult> <steps> <Gden> <lo1> <hi1> ...
 *        the same U at resolutions N0, N0*mult, ... (refinement ladder).
 *   ./gridcert search <N0> <m> [tries]
 *        U ranges over unions of N0-cells, evaluated at resolution N0*m:
 *        exhaustive for N0 <= 24 and m = 1, else randomized maximal-set search
 *        (deterministic PRNG, seed printed).  Goodness is downward closed.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

typedef int64_t  i64;
typedef uint64_t u64;

/* ------------------------------------------------------------ the SFT rule */

/* Successors of cell i at resolution N: j with cell j meeting the image of
 * cell i under y |-> (3y+e)/2.  Overlap test at denominator 2N:
 *   image(i,e) = [(3i+eN)/(2N), (3i+3+eN)/(2N)),  cell j = [2j/(2N),(2j+2)/(2N))
 *   overlap  <=>  2j < 3i+3+eN  and  3i+eN < 2j+2.
 * Returns the count; fills out[] with j and lab[] with e. */
static int succs(i64 i, i64 N, i64 *out, int *lab)
{
  int c = 0;
  for (int e = -2; e <= 1; e++) {
    i64 M = 3 * i + (i64)e * N;
    if (M + 3 <= 0 || M >= 2 * N) continue;        /* image outside [0,1) */
    for (i64 j = (M - 2) / 2 - 1; j <= (M + 3) / 2 + 1; j++) {
      if (j < 0 || j >= N) continue;
      if (2 * j < M + 3 && M < 2 * j + 2) { out[c] = j; lab[c] = e; c++; }
    }
  }
  return c;
}

/* Predecessors of cell j: i with 3i in (2j-2-eN, 2j+3-eN). */
static int preds(i64 j, i64 N, i64 *out)
{
  int c = 0;
  for (int e = -2; e <= 1; e++) {
    i64 base = 2 * j - (i64)e * N;
    for (i64 i = (base - 2) / 3 - 1; i <= (base + 3) / 3 + 1; i++) {
      if (i < 0 || i >= N) continue;
      i64 M = 3 * i + (i64)e * N;
      if (2 * j < M + 3 && M < 2 * j + 2) { out[c++] = i; }
    }
  }
  return c;
}

/* ------------------------------------------------------------------- U set */

typedef struct { i64 lo, hi; } rat_iv;         /* [lo/Gden, hi/Gden], closed */

/* cell i meets U?  (over-approximating: closed cell against closed interval) */
static int cell_meets(i64 i, i64 N, i64 Gden, const rat_iv *U, int nU)
{
  for (int t = 0; t < nU; t++)
    if (U[t].lo * N <= (i + 1) * Gden && i * Gden <= U[t].hi * N) return 1;
  return 0;
}

/* ------------------------------------------------------------------- peel */

/* Layered peel to the forward core.  alive[] in/out; returns peel depth and
 * the core size in *core. */
static i64 peel(unsigned char *alive, i64 N, i64 *core)
{
  i64 *out = malloc(16 * sizeof(i64)); int lab[16];
  i64 depth = 0, live = 0;
  for (i64 i = 0; i < N; i++) live += alive[i];
  unsigned char *kill = malloc((size_t)N);
  for (;;) {
    memset(kill, 0, (size_t)N);
    i64 nk = 0;
    for (i64 i = 0; i < N; i++) {
      if (!alive[i]) continue;
      int c = succs(i, N, out, lab), ok = 0;
      for (int t = 0; t < c; t++) if (alive[out[t]]) { ok = 1; break; }
      if (!ok) { kill[i] = 1; nk++; }
    }
    if (!nk) break;
    for (i64 i = 0; i < N; i++) if (kill[i]) alive[i] = 0;
    live -= nk; depth++;
    if (!live) break;
  }
  free(kill); free(out);
  *core = live;
  return depth;
}

/* ------------------------------------------------------- SCC (iterative Tarjan) */

typedef struct {
  i64 nscc, ncyclic, nbranch, biggest;
} scc_res;

static i64 *idx_, *low_, *comp_, *stk_, *dfs_, *edgeptr_;
static unsigned char *onstk_;

static void scc_analyse(unsigned char *alive, i64 N, scc_res *R)
{
  memset(R, 0, sizeof *R);
  idx_  = malloc((size_t)N * sizeof(i64));
  low_  = malloc((size_t)N * sizeof(i64));
  comp_ = malloc((size_t)N * sizeof(i64));
  stk_  = malloc((size_t)N * sizeof(i64));
  dfs_  = malloc((size_t)N * sizeof(i64));
  edgeptr_ = malloc((size_t)N * sizeof(i64));
  onstk_ = malloc((size_t)N);
  if (!onstk_) { fprintf(stderr, "oom in scc\n"); exit(1); }
  for (i64 i = 0; i < N; i++) { idx_[i] = -1; comp_[i] = -1; onstk_[i] = 0; }

  i64 counter = 0, sp = 0, nscc = 0;
  i64 out[16]; int lab[16];

  for (i64 root = 0; root < N; root++) {
    if (!alive[root] || idx_[root] >= 0) continue;
    i64 dp = 0;
    dfs_[dp] = root; edgeptr_[dp] = 0;
    idx_[root] = low_[root] = counter++;
    stk_[sp++] = root; onstk_[root] = 1;
    while (dp >= 0) {
      i64 v = dfs_[dp];
      int c = succs(v, N, out, lab);
      int advanced = 0;
      while (edgeptr_[dp] < c) {
        i64 w = out[edgeptr_[dp]++];
        if (!alive[w]) continue;
        if (idx_[w] < 0) {
          idx_[w] = low_[w] = counter++;
          stk_[sp++] = w; onstk_[w] = 1;
          dp++; dfs_[dp] = w; edgeptr_[dp] = 0;
          advanced = 1; break;
        } else if (onstk_[w]) {
          if (idx_[w] < low_[v]) low_[v] = idx_[w];
        }
      }
      if (advanced) continue;
      /* v finished */
      if (low_[v] == idx_[v]) {
        for (;;) {
          i64 w = stk_[--sp]; onstk_[w] = 0; comp_[w] = nscc;
          if (w == v) break;
        }
        nscc++;
      }
      dp--;
      if (dp >= 0) { i64 u = dfs_[dp]; if (low_[v] < low_[u]) low_[u] = low_[v]; }
    }
  }

  /* per-SCC: internal out-degree, size */
  i64 *size = calloc((size_t)nscc, sizeof(i64));
  unsigned char *branch = calloc((size_t)nscc, 1);
  unsigned char *cyclic = calloc((size_t)nscc, 1);
  for (i64 v = 0; v < N; v++) {
    if (!alive[v]) continue;
    size[comp_[v]]++;
    int c = succs(v, N, out, lab), internal = 0;
    for (int t = 0; t < c; t++) {
      i64 w = out[t];
      if (alive[w] && comp_[w] == comp_[v]) internal++;
    }
    if (internal >= 1) cyclic[comp_[v]] = 1;
    if (internal >= 2) branch[comp_[v]] = 1;
  }
  for (i64 s = 0; s < nscc; s++) {
    if (cyclic[s]) R->ncyclic++;
    if (branch[s]) R->nbranch++;
    if (size[s] > R->biggest) R->biggest = size[s];
  }
  R->nscc = nscc;
  free(size); free(branch); free(cyclic);
  free(idx_); free(low_); free(comp_); free(stk_); free(dfs_); free(edgeptr_);
  free(onstk_);
}

/* growth rate of the core adjacency (power iteration; diagnostics only) */
static double core_lambda(unsigned char *alive, i64 N, int iters)
{
  double *v = malloc((size_t)N * sizeof(double));
  double *w = malloc((size_t)N * sizeof(double));
  i64 out[16]; int lab[16];
  i64 live = 0;
  for (i64 i = 0; i < N; i++) { v[i] = alive[i] ? 1.0 : 0.0; live += alive[i]; }
  if (!live) { free(v); free(w); return 0.0; }
  double lam = 0;
  for (int it = 0; it < iters; it++) {
    for (i64 i = 0; i < N; i++) w[i] = 0.0;
    for (i64 i = 0; i < N; i++) {
      if (!alive[i]) continue;
      int c = succs(i, N, out, lab);
      for (int t = 0; t < c; t++) if (alive[out[t]]) w[i] += v[out[t]];
    }
    double nrm = 0;
    for (i64 i = 0; i < N; i++) nrm += w[i] * w[i];
    nrm = sqrt(nrm);
    if (nrm < 1e-300) { lam = 0; break; }
    double num = 0, den = 0;
    for (i64 i = 0; i < N; i++) { num += w[i] * v[i]; den += v[i] * v[i]; }
    lam = num / den;
    for (i64 i = 0; i < N; i++) v[i] = w[i] / nrm;
  }
  free(v); free(w);
  return lam;
}

/* --------------------------------------------------------------- one run */

typedef struct {
  i64 alive0, depth, core, nscc, ncyclic, nbranch, biggest;
  double lambda, len;
  const char *verd;
} run_res;

static void run_cert(i64 N, i64 Gden, const rat_iv *U, int nU, int want_scc,
                     run_res *R)
{
  unsigned char *alive = malloc((size_t)N);
  i64 a0 = 0;
  for (i64 i = 0; i < N; i++) { alive[i] = (unsigned char)cell_meets(i, N, Gden, U, nU); a0 += alive[i]; }
  R->alive0 = a0;
  R->len = 0;
  for (int t = 0; t < nU; t++) R->len += (double)(U[t].hi - U[t].lo) / (double)Gden;
  R->depth = peel(alive, N, &R->core);
  R->nscc = R->ncyclic = R->nbranch = R->biggest = 0;
  R->lambda = 0;
  if (getenv("GC_DUMP") && R->core) {
    i64 out[16]; int lab[16];
    fprintf(stderr, "# core at N=%lld:", (long long)N);
    for (i64 i = 0; i < N; i++) if (alive[i]) {
      fprintf(stderr, " %lld->{", (long long)i);
      int c = succs(i, N, out, lab);
      for (int t = 0; t < c; t++) if (alive[out[t]])
        fprintf(stderr, "%lld(e%d)", (long long)out[t], lab[t]);
      fprintf(stderr, "}");
    }
    fprintf(stderr, "\n");
  }
  if (R->core == 0) R->verd = "EMPTY";
  else if (want_scc) {
    scc_res S;
    scc_analyse(alive, N, &S);
    R->nscc = S.nscc; R->ncyclic = S.ncyclic; R->nbranch = S.nbranch;
    R->biggest = S.biggest;
    if (S.nbranch == 0) R->verd = "ZEROENT";
    else { R->lambda = core_lambda(alive, N, 200); R->verd = "BAND"; }
  } else R->verd = "CORE";
  free(alive);
}

/* --------------------------------------------------------- search (X3) */

/* bitmask engine for coarse cell-unions evaluated at resolution N0*m */
static i64 SN0, SM, SN;                   /* coarse cells, multiplier, N=N0*m */
static i64 *sc_out;                       /* successor lists at resolution SN */
static int *sc_cnt;

static void search_init(i64 N0, i64 m)
{
  SN0 = N0; SM = m; SN = N0 * m;
  sc_out = malloc((size_t)SN * 12 * sizeof(i64));
  sc_cnt = malloc((size_t)SN * sizeof(int));
  i64 out[16]; int lab[16];
  for (i64 i = 0; i < SN; i++) {
    int c = succs(i, SN, out, lab);
    sc_cnt[i] = c;
    for (int t = 0; t < c; t++) sc_out[i * 12 + t] = out[t];
  }
}

/* Is the union of coarse cells in `mask` good (EMPTY or ZEROENT) at resolution
 * SN?  Returns 0 = band, 1 = empty core, 2 = zero entropy. */
static unsigned char *sbuf = NULL;
static int search_good(u64 mask, i64 *core_out)
{
  if (!sbuf) sbuf = malloc((size_t)SN);
  for (i64 i = 0; i < SN; i++) sbuf[i] = (mask >> (i / SM)) & 1ULL;
  i64 core;
  peel(sbuf, SN, &core);
  *core_out = core;
  if (core == 0) return 1;
  scc_res S;
  scc_analyse(sbuf, SN, &S);
  return S.nbranch == 0 ? 2 : 0;
}

static u64 rngstate;
static u64 rnd(void) { rngstate ^= rngstate << 13; rngstate ^= rngstate >> 7;
                       rngstate ^= rngstate << 17; return rngstate; }

static void mode_search(i64 N0, i64 m, long tries)
{
  search_init(N0, m);
  printf("# X3 search: coarse cells N0=%lld, evaluated at N=%lld (m=%lld)\n",
         (long long)N0, (long long)SN, (long long)m);
  u64 best = 0; int bestpop = -1, bestkind = 0;
  i64 core;
  if (N0 <= 24 && tries == 0) {
    printf("# exhaustive over 2^%lld unions\n", (long long)N0);
    u64 total = 1ULL << N0;
    long ngood = 0;
    for (u64 mask = 0; mask < total; mask++) {
      int pop = __builtin_popcountll(mask);
      if (pop <= bestpop) continue;             /* only records interest us */
      int g = search_good(mask, &core);
      if (g) { ngood++; best = mask; bestpop = pop; bestkind = g; }
    }
    printf("# exhaustive done, records found: %ld\n", ngood);
  } else {
    rngstate = 0x2026072612345678ULL;
    printf("# randomized maximal-set search, seed 0x%llx, tries %ld\n",
           (unsigned long long)rngstate, tries);
    i64 perm[64];
    for (long t = 0; t < tries; t++) {
      for (i64 i = 0; i < N0; i++) perm[i] = i;
      for (i64 i = N0 - 1; i > 0; i--) { i64 j = (i64)(rnd() % (u64)(i + 1));
        i64 tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp; }
      u64 mask = 0; int kind = 1;
      for (i64 i = 0; i < N0; i++) {
        u64 cand = mask | (1ULL << perm[i]);
        int g = search_good(cand, &core);
        if (g) { mask = cand; kind = g; }
      }
      int pop = __builtin_popcountll(mask);
      if (pop > bestpop) { bestpop = pop; best = mask; bestkind = kind;
        printf("# try %ld: new best popcount %d (%s)\n", t, pop,
               kind == 1 ? "EMPTY" : "ZEROENT"); fflush(stdout); }
    }
  }
  printf("best union: popcount %d, total length %lld/%lld = %.6f, %s\n",
         bestpop, (long long)bestpop, (long long)N0, (double)bestpop / (double)N0,
         bestkind == 1 ? "EMPTY core" : "ZERO ENTROPY core");
  printf("cells:");
  for (i64 i = 0; i < N0; i++) if ((best >> i) & 1ULL) printf(" %lld", (long long)i);
  printf("\nintervals:");
  for (i64 i = 0; i < N0; i++) {
    if (!((best >> i) & 1ULL)) continue;
    if (i && ((best >> (i - 1)) & 1ULL)) continue;
    i64 j = i; while (j + 1 < N0 && ((best >> (j + 1)) & 1ULL)) j++;
    printf(" [%lld/%lld,%lld/%lld]", (long long)i, (long long)N0,
           (long long)(j + 1), (long long)N0);
  }
  printf("\n");
}

/* ------------------------------------------------------------------- main */

int main(int argc, char **argv)
{
  if (argc < 2) {
    fprintf(stderr,
      "usage: gridcert cert   <N> <Gden> <lo1> <hi1> [...]\n"
      "       gridcert ladder <N0> <mult> <steps> <Gden> <lo1> <hi1> [...]\n"
      "       gridcert search <N0> <m> [tries]\n");
    return 1;
  }
  if (!strcmp(argv[1], "search")) {
    mode_search(atol(argv[2]), argc > 3 ? atol(argv[3]) : 1,
                argc > 4 ? atol(argv[4]) : 0);
    return 0;
  }
  int base = !strcmp(argv[1], "ladder") ? 5 : 3;
  i64 N   = atol(argv[2]);
  i64 mult = 1, steps = 1;
  if (base == 5) { mult = atol(argv[3]); steps = atol(argv[4]); }
  i64 Gden = atol(argv[base]);
  int nU = (argc - base - 1) / 2;
  if (nU <= 0) { fprintf(stderr, "no intervals given\n"); return 1; }
  rat_iv *U = malloc(sizeof(rat_iv) * (size_t)nU);
  for (int t = 0; t < nU; t++) {
    U[t].lo = atol(argv[base + 1 + 2 * t]);
    U[t].hi = atol(argv[base + 2 + 2 * t]);
  }
  printf("# U =");
  for (int t = 0; t < nU; t++)
    printf(" [%lld/%lld,%lld/%lld]", (long long)U[t].lo, (long long)Gden,
           (long long)U[t].hi, (long long)Gden);
  double len = 0;
  for (int t = 0; t < nU; t++) len += (double)(U[t].hi - U[t].lo) / (double)Gden;
  printf("   |U| = %.6f\n", len);
  printf("# N  alive  peeldepth  core  SCC  cyclic  branching  lambda  verdict\n");
  for (i64 st = 0; st < steps; st++) {
    run_res R;
    run_cert(N, Gden, U, nU, 1, &R);
    printf("%lld %lld %lld %lld %lld %lld %lld %.6f %s\n",
           (long long)N, (long long)R.alive0, (long long)R.depth,
           (long long)R.core, (long long)R.nscc, (long long)R.ncyclic,
           (long long)R.nbranch, R.lambda, R.verd);
    fflush(stdout);
    N *= mult;
  }
  return 0;
}
