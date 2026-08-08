/* (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
 *
 * atlas.c -- plan-cert32 milestone M2, ENGINE C (the atlas engine):
 *            EXACT rational hold-set pruning for an arbitrary finite union U of
 *            rational intervals, plus the functional-graph ("zero entropy")
 *            certificate.  This is the engine the atlas is built from; hold.c
 *            (theta-coordinates, single windows) and gridcert.c (uniform cell
 *            SFT) are independent cross-checks.
 *
 * MODEL (plan §1.1), in y-coordinates directly -- no decoupling needed:
 *
 *     y_{n+1} = (3 y_n + e_n)/2,   e_n = 3 x_n - 2 x_{n+1} in {-2,-1,0,1},
 *
 * y_n = {xi (3/2)^n}.  Confinement to U means y_n in U for all n.  Set
 *
 *     S_0 = U,   S_{k+1} = U cap f^{-1}(S_k),   f^{-1}(A) = union_e (2A-e)/3,
 *
 * so S_k = { y in U : some admissible continuation stays in U for k steps }.
 * Everything is exact: level k lives over the denominator D_k = Gden * 3^k and
 * all arithmetic is __int128 integer arithmetic.  U is half-open, [lo,hi),
 * the corpus Ico convention (FLP.ZSet).  To certify a CLOSED union, inflate the
 * right endpoints by one unit of a finer denominator -- certifying the larger
 * half-open set certifies the closed subset.
 *
 * THE TWO CERTIFICATES.
 *
 *   KILL n     S_n = empty.  UNCONDITIONAL: no xi > 0 has {xi(3/2)^n} in U for
 *              all n.  (Z_ev(U) = empty too, by the shift trick of
 *              FLP/Capstone.lean.)
 *
 *   CYCLE      S_k is a disjoint union of c exact intervals C_1..C_c and the
 *              transition relation
 *                   i -> j  iff  (3*C_i + e)/2 meets C_j for some e
 *              is a PARTIAL FUNCTION (out-degree <= 1, and the carry e is then
 *              determined by i).  A confined orbit is a path in a functional
 *              graph, hence eventually periodic, hence its carry word
 *              e_n = -(q x_{n+1} - p x_n) is eventually periodic -- which is
 *              false for EVERY xi != 0 by Z32.not_isEventuallyPeriodic_carry
 *              (= [DN05] Lemma 2, proved in the corpus, std3).  So Z(U) = empty.
 *
 *              This is DubC's C(P) certificate ("no branching SCC") transplanted
 *              to the fractional side, and it is what covers the FLP positions,
 *              whose survivor set is a nonempty finite cycle.  A uniform cell
 *              grid can never see this: the image of a cell is 1.5 cells wide,
 *              so a true cycle always looks branching (see gridcert.c).
 *
 *   FAT        the component count grows: the survivor set is an infinite
 *              Cantor set and the engine decides nothing.  lambda = growth rate
 *              of the component count; dim_box <= log lambda / log(3/2) is the
 *              T5 dimension datum.  Reported, never hidden.
 *
 * Build: gcc -O2 -o atlas atlas.c -lm
 * Modes:
 *   ./atlas cert <depth> <Gden> <lo1> <hi1> [<lo2> <hi2> ...]
 *   ./atlas win  <depth> <G> <a> <b>            U = [a/G,(a+b)/G)  (single window)
 *   ./atlas x2   <G> <jlo> <jhi> <depth>        length sweep, y-model
 *   ./atlas x3   <N0> <tries> <depth>           randomized maximal-union search
 *   ./atlas x3exh <N0> <depth>                  exhaustive union search (N0<=22)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

typedef __int128 i128;
typedef int64_t  i64;
typedef uint64_t u64;

static const i128 SAFE = ((i128)1) << 120;

typedef struct { i128 A, B; } iv;

static void p128(char *b, i128 v);

/* ------------------------------------------------------------- the engine */

#define MAXC 262144
#define TAIL 6

typedef struct {
  long depth, kill, comps, capped, cyclecert, outdeg_max, blocks;
  double meas, lambda;
  long comps_at[512];
  /* the certificate, when cyclecert = 1 */
  long cyc_c;
  iv   cyc[64];
  i128 cyc_D;
  int  cyc_e[64];
  long cyc_next[64];
} res;

/* intersect sorted list a[0..na) with sorted list b[0..nb) (both over the same
 * denominator, disjoint, ascending); result into out, returns count. */
static long isect(const iv *a, long na, const iv *b, long nb, iv *out, long cap)
{
  long i = 0, j = 0, m = 0;
  while (i < na && j < nb) {
    i128 lo = a[i].A > b[j].A ? a[i].A : b[j].A;
    i128 hi = a[i].B < b[j].B ? a[i].B : b[j].B;
    if (lo < hi) {
      if (m && out[m-1].B >= lo) { if (out[m-1].B < hi) out[m-1].B = hi; }
      else { if (m >= cap) return -1; out[m].A = lo; out[m].B = hi; m++; }
    }
    if (a[i].B < b[j].B) i++; else j++;
  }
  return m;
}

/* one pruning run.  U given over Gden as nU disjoint ascending [lo,hi). */
static void prune(const i64 *Ulo, const i64 *Uhi, int nU, i64 Gden,
                  long depth, long cap, res *R)
{
  memset(R, 0, sizeof *R);
  R->kill = -1;
  static iv cur[MAXC], nxt[MAXC], pre[MAXC], Us[64];
  if (depth > 500) depth = 500;

  i128 D = Gden, P3 = 1;
  long n = 0;
  for (int t = 0; t < nU; t++) { cur[n].A = Ulo[t]; cur[n].B = Uhi[t]; n++; }
  R->comps_at[0] = n;
  double m0 = 0;
  for (long t = 0; t < n; t++) m0 += (double)(cur[t].B - cur[t].A);
  R->meas = m0 / (double)D; R->comps = n;

  for (long k = 0; k < depth; k++) {
    if (n == 0) break;
    if (4 * D * 3 > SAFE) { R->capped = 2; break; }
    i128 Dn = 3 * D;
    P3 *= 3;
    /* Preimages.  For a fixed carry e the images of the (ascending) source list
     * are ascending, but the ranges for different e OVERLAP: the preimage of
     * [0,1) under e is [-e/3,(2-e)/3), width 2/3, while consecutive e are only
     * 1/3 apart.  (For a single window of length <= 1/2 they happen to be
     * disjoint, which is why the theta-model of hold.c can merge naively.)  So
     * the four sorted runs must be merged properly. */
    long m = 0;
    {
      const int es[4] = {1, 0, -1, -2};
      long ptr[4]; i128 hA[4], hB[4]; int have[4];
      for (int z = 0; z < 4; z++) { ptr[z] = 0; have[z] = 0; }
      for (int z = 0; z < 4; z++)
        while (ptr[z] < n) {
          i128 A = 2 * cur[ptr[z]].A - (i128)es[z] * D;
          i128 B = 2 * cur[ptr[z]].B - (i128)es[z] * D;
          ptr[z]++;
          if (A < 0) A = 0;
          if (B > Dn) B = Dn;
          if (A < B) { hA[z] = A; hB[z] = B; have[z] = 1; break; }
        }
      for (;;) {
        int best = -1;
        for (int z = 0; z < 4; z++)
          if (have[z] && (best < 0 || hA[z] < hA[best])) best = z;
        if (best < 0) break;
        i128 A = hA[best], B = hB[best];
        if (m && pre[m-1].B >= A) { if (pre[m-1].B < B) pre[m-1].B = B; }
        else { if (m >= MAXC) { R->capped = 1; break; } pre[m].A = A; pre[m].B = B; m++; }
        have[best] = 0;
        while (ptr[best] < n) {
          i128 A2 = 2 * cur[ptr[best]].A - (i128)es[best] * D;
          i128 B2 = 2 * cur[ptr[best]].B - (i128)es[best] * D;
          ptr[best]++;
          if (A2 < 0) A2 = 0;
          if (B2 > Dn) B2 = Dn;
          if (A2 < B2) { hA[best] = A2; hB[best] = B2; have[best] = 1; break; }
        }
      }
    }
    if (R->capped) break;
    for (int t = 0; t < nU; t++) { Us[t].A = (i128)Ulo[t] * P3; Us[t].B = (i128)Uhi[t] * P3; }
    long q = isect(pre, m, Us, nU, nxt, MAXC);
    if (q < 0) { R->capped = 1; break; }
    memcpy(cur, nxt, sizeof(iv) * (size_t)q);
    n = q; D = Dn;
    R->depth = k + 1;
    double meas = 0;
    for (long t = 0; t < n; t++) meas += (double)(cur[t].B - cur[t].A);
    R->meas = meas / (double)D;
    R->comps = n;
    if (k + 1 < 512) R->comps_at[k+1] = n;
    if (n == 0) { R->kill = k + 1; break; }
    if (n > cap) { R->capped = 1; break; }
  }

  long d = R->depth;
  if (R->kill < 0 && !R->capped && d >= TAIL && d < 512) {
    long c0 = R->comps_at[d - TAIL], c1 = R->comps_at[d];
    R->lambda = c0 > 0 ? pow((double)c1 / (double)c0, 1.0 / (double)TAIL) : 0;
  }

  /* ---- the CYCLE certificate ----------------------------------------------
   * Group the components into BLOCKS (consecutive runs, so every block hull is
   * an interval and hulls are disjoint) until the induced transition relation
   * on block hulls is a partial function with a determined carry.  Merging is
   * the fixpoint of: "if the image of one block hull meets two blocks, merge
   * them".  Coarsening is always sound -- a bigger hull can only add
   * transitions -- so a surviving certificate is genuine.
   *
   * Why blocks and not components: above L = 1/3 an exact periodic point is
   * hugged, at EVERY depth, by a cluster of surviving intervals which shrinks
   * onto it; the raw component graph therefore never becomes functional even
   * when the survivor set is a single finite cycle.  The block fixpoint is what
   * sees the cycle.  */
  if (R->kill < 0 && !R->capped && n > 0 && n <= 4096) {
    char *brk = malloc((size_t)n);       /* brk[i]=1: block boundary before i */
    for (long i = 0; i < n; i++) brk[i] = 1;
    /* first component with 2*C.B > x (binary search; components ascending) */
    long lo_, hi_, mid_;
    for (long round = 0; round < 200; round++) {
      int changed = 0;
      for (long a = 0; a < n; ) {
        long b = a + 1;
        while (b < n && !brk[b]) b++;               /* block = components a..b-1 */
        i128 hA = cur[a].A, hB = cur[b-1].B;
        for (int e = -2; e <= 1; e++) {
          i128 lo = 3 * hA + (i128)e * D, hi = 3 * hB + (i128)e * D;
          if (hi <= 0 || lo >= 2 * D) continue;
          lo_ = 0; hi_ = n;
          while (lo_ < hi_) { mid_ = (lo_ + hi_) / 2;
            if (2 * cur[mid_].B > lo) hi_ = mid_; else lo_ = mid_ + 1; }
          long first = -1, last = -1;
          for (long j = lo_; j < n && 2 * cur[j].A < hi; j++) {
            if (first < 0) first = j;
            last = j;
          }
          if (first < 0) continue;
          for (long j = first + 1; j <= last; j++)
            if (brk[j]) { brk[j] = 0; changed = 1; }
        }
        a = b;
      }
      if (!changed) break;
    }
    /* final check on the block graph */
    long m = 0;
    for (long i = 0; i < n; i++) if (brk[i]) m++;
    long *bs = malloc((size_t)(m + 1) * sizeof(long));
    long t = 0;
    for (long i = 0; i < n; i++) if (brk[i]) bs[t++] = i;
    bs[m] = n;
    /* block index of the component containing position j */
    int ok = 1; long maxdeg = 0;
    for (long i = 0; i < m && ok; i++) {
      i128 hA = cur[bs[i]].A, hB = cur[bs[i+1]-1].B;
      long deg = 0, nxtj = -1; int nxte = 0;
      for (int e = -2; e <= 1; e++) {
        i128 lo = 3 * hA + (i128)e * D, hi = 3 * hB + (i128)e * D;
        if (hi <= 0 || lo >= 2 * D) continue;
        for (long j = 0; j < m; j++) {
          i128 cl = 2 * cur[bs[j]].A, ch = 2 * cur[bs[j+1]-1].B;
          if (ch <= lo) continue;
          if (cl >= hi) break;
          deg++; nxtj = j; nxte = e;
        }
      }
      if (deg > maxdeg) maxdeg = deg;
      if (deg > 1) ok = 0;
      else if (i < 64) { R->cyc_next[i] = nxtj; R->cyc_e[i] = nxte; }
    }
    R->outdeg_max = maxdeg;
    R->blocks = m;
    if (ok && m <= 64) {
      R->cyclecert = 1; R->cyc_c = m; R->cyc_D = D;
      for (long i = 0; i < m; i++) {
        R->cyc[i].A = cur[bs[i]].A; R->cyc[i].B = cur[bs[i+1]-1].B;
      }
    } else if (ok) { R->cyclecert = 1; R->cyc_c = 0; R->cyc_D = D; }
    free(brk); free(bs);
  }
  if (getenv("ATLAS_COMPS") && n && n < 200) {
    char b1[48], b2[48], b3[48]; p128(b3, D);
    fprintf(stderr, "# %ld components over %s:\n", n, b3);
    for (long i = 0; i < n; i++) {
      p128(b1, cur[i].A); p128(b2, cur[i].B);
      fprintf(stderr, "  C%ld = [%s,%s)  ~ %.15f .. %.15f\n", i, b1, b2,
              (double)cur[i].A / (double)D, (double)cur[i].B / (double)D);
    }
  }
}

static const char *verdict(const res *R)
{
  if (R->kill >= 0)   return "KILL";
  if (R->cyclecert)   return "CYCLE";
  if (R->capped == 1) return "CAP";
  if (R->capped == 2) return "PREC";
  return "FAT";
}
static int certified(const res *R) { return R->kill >= 0 || R->cyclecert; }

static void p128(char *b, i128 v)
{ char t[48]; int n=0,m=0,g=0; if(v<0){g=1;v=-v;} if(!v)t[n++]='0';
  while(v){t[n++]=(char)('0'+(int)(v%10));v/=10;} if(g)b[m++]='-';
  while(n)b[m++]=t[--n]; b[m]=0; }

/* ------------------------------------------------------------------ modes */

static void report(const res *R, int full)
{
  if (full) {
    printf("# level  components  \n");
    for (long k = 0; k <= R->depth && k < 512; k++)
      printf("  %4ld  %10ld\n", k, R->comps_at[k]);
  }
  printf("verdict %s  kill %ld  depth %ld  comps %ld  blocks %ld  meas %.6g  lambda %.6f  maxoutdeg %ld\n",
         verdict(R), R->kill, R->depth, R->comps, R->blocks, R->meas, R->lambda, R->outdeg_max);
  if (R->cyclecert) {
    char b1[48], b2[48], b3[48];
    p128(b3, R->cyc_D);
    printf("CERTIFICATE: %ld components over denominator %s, functional graph\n",
           R->cyc_c, b3);
    for (long i = 0; i < R->cyc_c; i++) {
      p128(b1, R->cyc[i].A); p128(b2, R->cyc[i].B);
      printf("  C%ld = [%s,%s)/%s  --e=%d-->  C%ld\n", i, b1, b2, b3,
             R->cyc_e[i], R->cyc_next[i]);
    }
  }
}

static void mode_cert(long depth, i64 Gden, const i64 *lo, const i64 *hi, int nU,
                      int full)
{
  double len = 0;
  printf("# U =");
  for (int t = 0; t < nU; t++) {
    printf(" [%lld/%lld,%lld/%lld)", (long long)lo[t], (long long)Gden,
           (long long)hi[t], (long long)Gden);
    len += (double)(hi[t] - lo[t]) / (double)Gden;
  }
  printf("   |U| = %.9f\n", len);
  res R;
  prune(lo, hi, nU, Gden, depth, MAXC - 8, &R);
  report(&R, full);
}

/* X2: the (position,length) map in y-coordinates (cross-check of hold.c) */
static void mode_x2(i64 G, i64 jlo, i64 jhi, long depth)
{
  long x2cap = getenv("ATLAS_CAP") ? atol(getenv("ATLAS_CAP")) : 200000;
  printf("# X2 (y-model)  G=%lld  L=j/G  depth=%ld cap=%ld\n", (long long)G, depth, x2cap);
  printf("# j i kill comps lambda maxoutdeg verdict\n");
  for (i64 j = jlo; j <= jhi; j++) {
    long nk = 0, ncyc = 0, nfat = 0, ncap = 0, tot = 0;
    double lmin = 1e9, lmax = 0;
    i64 ilo = getenv("ATLAS_ILO") ? atol(getenv("ATLAS_ILO")) : 0;
    i64 ihi = getenv("ATLAS_IHI") ? atol(getenv("ATLAS_IHI")) : G;
    for (i64 i = ilo; i + j <= G && i <= ihi; i++) {
      i64 lo = i, hi = i + j;
      res R;
      prune(&lo, &hi, 1, G, depth, x2cap, &R);
      const char *v = verdict(&R);
      printf("%lld %lld %ld %ld %.4f %ld %s\n", (long long)j, (long long)i,
             R.kill, R.comps, R.lambda, R.outdeg_max, v);
      tot++;
      if (R.kill >= 0) nk++;
      else if (R.cyclecert) ncyc++;
      else if (R.capped) ncap++;
      else { nfat++; if (R.lambda < lmin) lmin = R.lambda;
             if (R.lambda > lmax) lmax = R.lambda; }
    }
    printf("# row j=%lld L=%.6f n=%ld KILL=%ld CYCLE=%ld FAT=%ld CAP=%ld certified=%ld lambda[%.4f,%.4f]\n",
           (long long)j, (double)j / (double)G, tot, nk, ncyc, nfat, ncap,
           nk + ncyc, nfat ? lmin : 0.0, lmax);
    fflush(stdout);
  }
}

/* ------------------------------------------------------- X3: union search */

static long X3_N0, X3_DEPTH;

/* mask of N0 cells -> is the union certified?  0 no, 1 KILL, 2 CYCLE */
static int mask_good(u64 mask, long *comps, double *lam)
{
  i64 lo[64], hi[64]; int nU = 0;
  for (long i = 0; i < X3_N0; i++) {
    if (!((mask >> i) & 1ULL)) continue;
    if (nU && hi[nU-1] == i) hi[nU-1] = i + 1;
    else { lo[nU] = i; hi[nU] = i + 1; nU++; }
  }
  if (!nU) { *comps = 0; *lam = 0; return 1; }
  res R;
  prune(lo, hi, nU, X3_N0, X3_DEPTH, 100000, &R);
  *comps = R.comps; *lam = R.lambda;
  if (R.kill >= 0) return 1;
  if (R.cyclecert) return 2;
  return 0;
}

static u64 rngstate;
static u64 rnd(void){ rngstate^=rngstate<<13; rngstate^=rngstate>>7;
                      rngstate^=rngstate<<17; return rngstate; }

static void print_union(u64 mask, long N0)
{
  printf("U =");
  for (long i = 0; i < N0; i++) {
    if (!((mask >> i) & 1ULL)) continue;
    if (i && ((mask >> (i-1)) & 1ULL)) continue;
    long j = i; while (j + 1 < N0 && ((mask >> (j+1)) & 1ULL)) j++;
    printf(" [%ld/%ld,%ld/%ld)", i, N0, j + 1, N0);
  }
  printf("\n");
}

static void mode_x3(long N0, long tries, long depth)
{
  X3_N0 = N0; X3_DEPTH = depth;
  rngstate = 0x2026072612345678ULL;
  printf("# X3 randomized maximal-union search: N0=%ld cells, depth=%ld, tries=%ld, seed 0x%llx\n",
         N0, depth, tries, (unsigned long long)rngstate);
  u64 best = 0; long bestpop = -1; int bestkind = 0;
  long comps; double lam;
  i64 perm[64];
  for (long t = 0; t < tries; t++) {
    for (long i = 0; i < N0; i++) perm[i] = i;
    for (long i = N0 - 1; i > 0; i--) { long j = (long)(rnd() % (u64)(i+1));
      i64 tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp; }
    u64 mask = 0; int kind = 1;
    for (long i = 0; i < N0; i++) {
      u64 cand = mask | (1ULL << perm[i]);
      int g = mask_good(cand, &comps, &lam);
      if (g) { mask = cand; kind = g; }
    }
    long pop = __builtin_popcountll(mask);
    if (pop > bestpop) {
      bestpop = pop; best = mask; bestkind = kind;
      printf("# try %ld: popcount %ld = %.6f  (%s)  ", t, pop,
             (double)pop / (double)N0, kind == 1 ? "KILL" : "CYCLE");
      print_union(mask, N0);
      fflush(stdout);
    }
  }
  printf("BEST total length %ld/%ld = %.9f  (%s)\n", bestpop, N0,
         (double)bestpop / (double)N0, bestkind == 1 ? "KILL" : "CYCLE");
  print_union(best, N0);
}

static void mode_x3exh(long N0, long depth)
{
  X3_N0 = N0; X3_DEPTH = depth;
  printf("# X3 exhaustive union search: N0=%ld cells, depth=%ld, 2^%ld unions\n",
         N0, depth, N0);
  u64 best = 0; long bestpop = -1; int bestkind = 0; long nrec = 0;
  long comps; double lam;
  u64 total = 1ULL << N0;
  for (u64 mask = 0; mask < total; mask++) {
    long pop = __builtin_popcountll(mask);
    if (pop <= bestpop) continue;
    int g = mask_good(mask, &comps, &lam);
    if (g) { best = mask; bestpop = pop; bestkind = g; nrec++;
      printf("# record popcount %ld = %.6f (%s)  ", pop,
             (double)pop / (double)N0, g == 1 ? "KILL" : "CYCLE");
      print_union(mask, N0); fflush(stdout); }
  }
  printf("BEST total length %ld/%ld = %.9f  (%s), records %ld\n", bestpop, N0,
         (double)bestpop / (double)N0, bestkind == 1 ? "KILL" : "CYCLE", nrec);
  print_union(best, N0);
}

/* ------------------------------------------- horseshoes: the rigorous no-go */

/* A period-P orbit of y |-> (3y+e)/2 with carry word w satisfies
 *      y_0 = -(sum_i 3^{P-1-i} 2^i w_i) / (3^P - 2^P),
 * so every cycle of the hold dynamics is an explicit rational.  Enumerating all
 * carry words of length <= P and keeping those whose whole orbit lies in U
 * finds every short cycle exactly.  If two DISTINCT cycles pass through a
 * common point y*, there are two different admissible ways from y* back to y*,
 * so the confined orbits of the model are uncountable -- and NO argument that
 * looks only at the archimedean hold set can prove Z(U) = empty.  That is a
 * theorem about the method, not a failure of it: such an entry needs the dyadic
 * refinement (plan §4.3), and it is why the band is data, not a gap.          */

typedef struct { i128 num, den; } rat;

static int rat_eq(rat a, rat b){ return a.num * b.den == b.num * a.den; }

static int in_U(rat y, const i64 *lo, const i64 *hi, int nU, i64 Gden)
{
  for (int t = 0; t < nU; t++)
    if (y.num * Gden >= (i128)lo[t] * y.den && y.num * Gden < (i128)hi[t] * y.den)
      return 1;
  return 0;
}

static rat rat_step(rat z, int e)
{
  rat nz; nz.num = 3 * z.num + (i128)e * z.den; nz.den = 2 * z.den;
  while (!(nz.num & 1) && !(nz.den & 1)) { nz.num /= 2; nz.den /= 2; }
  return nz;
}

static void mode_horseshoe(long maxP, i64 Gden, const i64 *lo, const i64 *hi, int nU)
{
  printf("# horseshoe search, periods 1..%ld, U =", maxP);
  for (int t = 0; t < nU; t++)
    printf(" [%lld/%lld,%lld/%lld)", (long long)lo[t], (long long)Gden,
           (long long)hi[t], (long long)Gden);
  printf("\n");
  static rat pts[400000]; static long cid[400000];
  static rat cpt[4096][24]; static int cw[4096][24]; static long clen[4096];
  long npts = 0, ncyc = 0;
  char b1[48], b2[48];
  for (long P = 1; P <= maxP; P++) {
    i128 p3 = 1, p2 = 1;
    for (long i = 0; i < P; i++) { p3 *= 3; p2 *= 2; }
    i128 M = p3 - p2;
    long total = 1; for (long i = 0; i < P; i++) total *= 4;
    for (long code = 0; code < total; code++) {
      int w[24]; long c = code;
      for (long i = 0; i < P; i++) { w[i] = (int)(c & 3) - 2; c >>= 2; }
      i128 S = 0;
      for (long i = 0; i < P; i++) {
        i128 a = 1, b = 1;
        for (long z = 0; z < P - 1 - i; z++) a *= 3;
        for (long z = 0; z < i; z++) b *= 2;
        S += a * b * (i128)w[i];
      }
      rat y; y.num = -S; y.den = M;
      if (y.num < 0 || y.num >= y.den) continue;
      rat z = y; int ok = 1;
      for (long i = 0; i < P && ok; i++) {
        if (!in_U(z, lo, hi, nU, Gden)) { ok = 0; break; }
        rat nz = rat_step(z, w[i]);
        if (nz.num < 0 || nz.num >= nz.den) { ok = 0; break; }
        z = nz;
      }
      if (!ok || !rat_eq(z, y)) continue;
      /* canonicalise: rotate so the orbit's minimal point comes first, then
       * reduce to the primitive period -- otherwise every cycle reappears once
       * per rotation and once per repetition, and two copies of one cycle would
       * masquerade as a horseshoe. */
      rat orb[24]; int ww[24];
      { rat q = y;
        for (long i = 0; i < P; i++) { orb[i] = q; ww[i] = w[i]; q = rat_step(q, w[i]); } }
      long mi = 0;
      for (long i = 1; i < P; i++)
        if (orb[i].num * orb[mi].den < orb[mi].num * orb[i].den) mi = i;
      rat rorb[24]; int rw[24];
      for (long i = 0; i < P; i++) { rorb[i] = orb[(mi + i) % P]; rw[i] = ww[(mi + i) % P]; }
      long d = P;
      for (long e2 = 1; e2 < P; e2++) {
        if (P % e2) continue;
        int per = 1;
        for (long i = 0; i < P && per; i++) if (rw[i] != rw[i % e2]) per = 0;
        if (per) { d = e2; break; }
      }
      /* already seen? */
      long myid = -1;
      for (long c2 = 0; c2 < ncyc; c2++)
        if (clen[c2] == d) {
          int same = 1;
          for (long i = 0; i < d && same; i++)
            if (!rat_eq(cpt[c2][i], rorb[i]) || cw[c2][i] != rw[i]) same = 0;
          if (same) { myid = c2; break; }
        }
      if (myid >= 0) continue;
      myid = ncyc++;
      if (myid >= 4096) { printf("# cycle table full\n"); break; }
      clen[myid] = d;
      for (long i = 0; i < d; i++) { cpt[myid][i] = rorb[i]; cw[myid][i] = rw[i]; }
      for (long i = 0; i < d; i++) {
        if (npts < 400000) { pts[npts] = rorb[i]; cid[npts] = myid; npts++; }
      }
    }
  }
  printf("cycles found: %ld  (orbit points %ld)\n", ncyc, npts);
  for (long i = 0; i < npts; i++)
    for (long j = i + 1; j < npts; j++)
      if (cid[i] != cid[j] && rat_eq(pts[i], pts[j])) {
        p128(b1, pts[i].num); p128(b2, pts[i].den);
        printf("HORSESHOE at y = %s/%s ~ %.12f : two distinct cycles (%ld, %ld) meet there\n",
               b1, b2, (double)pts[i].num / (double)pts[i].den, cid[i], cid[j]);
        printf("=> the confined orbits of the interval model are uncountable; no hold-set-only\n"
               "   argument can certify this U -- it needs the dyadic refinement (plan 4.3).\n");
        return;
      }
  printf("no horseshoe up to period %ld\n", maxP);
}

int main(int argc, char **argv)
{
  if (argc < 2) {
    fprintf(stderr,
      "usage: atlas cert  <depth> <Gden> <lo1> <hi1> [...]\n"
      "       atlas win   <depth> <G> <a> <b>\n"
      "       atlas x2    <G> <jlo> <jhi> <depth>\n"
      "       atlas x3    <N0> <tries> <depth>\n"
      "       atlas x3exh <N0> <depth>\n");
    return 1;
  }
  if (!strcmp(argv[1], "cert") && argc >= 6) {
    long depth = atol(argv[2]); i64 Gden = atol(argv[3]);
    int nU = (argc - 4) / 2;
    i64 lo[64], hi[64];
    for (int t = 0; t < nU; t++) { lo[t] = atol(argv[4 + 2*t]); hi[t] = atol(argv[5 + 2*t]); }
    mode_cert(depth, Gden, lo, hi, nU, getenv("ATLAS_FULL") != NULL);
  } else if (!strcmp(argv[1], "win") && argc >= 6) {
    long depth = atol(argv[2]); i64 G = atol(argv[3]);
    i64 lo = atol(argv[4]), hi = lo + atol(argv[5]);
    mode_cert(depth, G, &lo, &hi, 1, getenv("ATLAS_FULL") != NULL);
  } else if (!strcmp(argv[1], "x2") && argc >= 6) {
    mode_x2(atol(argv[2]), atol(argv[3]), atol(argv[4]), atol(argv[5]));
  } else if (!strcmp(argv[1], "x3") && argc >= 5) {
    mode_x3(atol(argv[2]), atol(argv[3]), atol(argv[4]));
  } else if (!strcmp(argv[1], "horse") && argc >= 6) {
    long P = atol(argv[2]); i64 Gden = atol(argv[3]);
    int nU = (argc - 4) / 2; i64 lo[64], hi[64];
    for (int t = 0; t < nU; t++) { lo[t] = atol(argv[4 + 2*t]); hi[t] = atol(argv[5 + 2*t]); }
    mode_horseshoe(P, Gden, lo, hi, nU);
  } else if (!strcmp(argv[1], "x3exh") && argc >= 4) {
    mode_x3exh(atol(argv[2]), atol(argv[3]));
  } else { fprintf(stderr, "bad arguments\n"); return 1; }
  return 0;
}
