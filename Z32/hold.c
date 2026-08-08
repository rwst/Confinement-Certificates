/* (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
 *
 * hold.c -- plan-cert32 milestone M2, ENGINE A:
 *           exact rational hold-set pruning for single windows [s, s+L).
 *
 * MODEL (plan §1.3(i) = FLP95 Prop 2.1, formalized in FLP/Decoupling.lean).
 * For p/q = 3/2 and a window [s, s+L) with L <= 1/2 write
 *
 *     theta_n = q*({xi (p/q)^n} - s) = 2*({xi (3/2)^n} - s)  in  [0, qL) = [0, 2L),
 *
 * (FLP.thetaPart).  The decoupling identity gives the DETERMINISTIC recursion
 *
 *     theta_{n+1} = f(theta_n),   f(x) = frac(beta*x + alpha),
 *     beta = 3/2,  alpha = frac((p-q)s) = s     (FLP.alphaSym, p-q = 1),
 *
 * and confinement of the real orbit to [s, s+L) is exactly survival of theta
 * inside J = [0, T),  T = qL = 2L.  At L = 1/3 this is T = 2/3 = 1/beta, i.e.
 * FLP's own survivor set `FLP.survivors (3/2) s` -- the L > 1/3 territory is the
 * plan's new zone (§4.1).
 *
 * WHAT IS COMPUTED.  S_0 = J,  S_{k+1} = J cap f^{-1}(S_k), i.e.
 *
 *     S_k = { x in J : f^j(x) in J for all j <= k },
 *
 * as an EXACT finite union of half-open rational intervals.  Level k lives over
 * the common denominator D_k = G*3^k (G = the denominator of s and L), so all
 * arithmetic is integer arithmetic in __int128 -- no floating point anywhere in
 * the decision path.  Reported per level: the number of connected components and
 * the total measure.  Verdicts:
 *
 *   KILL n    S_n = empty.  UNCONDITIONAL: no real xi has its orbit in [s,s+L).
 *   FIN       component count stable, measure -> 0 geometrically: the survivor
 *             set is finite.  Emptiness then needs FLP95 Thm 3.2, which is
 *             formalized at L = 1/3 (FLP.ZSet_eq_empty_of_survivors_finite) and
 *             is the plan's §4.1(a) generalization above 1/3.
 *   FAT       component count grows: survivor set infinite (Cantor).  Engine A
 *             decides nothing; the growth rate lambda is T5 dimension data
 *             (dim_box = log lambda / log(3/2)).
 *
 * Also computed, as the cheap diagnostic that FLP's finiteness criterion uses:
 * the escape depths of the two kneading orbits, that of 0 and that of T^- (they
 * coincide when T = 1/beta, i.e. exactly at L = 1/3, which is why FLP need only
 * one).  `esc0` is FLP95's own witness: f^N(0) >= 1/beta.
 *
 * Build:  gcc -O2 -o hold hold.c
 * Modes:  ./hold orbit  <a> <b> <G> [maxn]     escape orbits of 0 and T^-
 *         ./hold prune  <a> <b> <G> [depth]    per-level pruning trace
 *         ./hold x1     <G> [depth]            X1: L = 1/3, all s = i/G
 *         ./hold x2     <G> <jlo> <jhi> [depth] X2: L = j/G, all s = i/G
 * where s = a/G, L = b/G (window [s, s+L), so a + b <= G and 2b <= G).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

typedef __int128 i128;

/* Safety ceiling: every intermediate is bounded by 6*D_k, so we stop a level
 * before 6*D_k could reach 2^120.  No silent wraparound. */
static const i128 SAFE = ((i128)1) << 120;

static void p128(char *buf, i128 v)
{
  char tmp[48]; int n = 0, neg = 0;
  if (v < 0) { neg = 1; v = -v; }
  if (!v) tmp[n++] = '0';
  while (v) { tmp[n++] = (char)('0' + (int)(v % 10)); v /= 10; }
  int m = 0;
  if (neg) buf[m++] = '-';
  while (n) buf[m++] = tmp[--n];
  buf[m] = 0;
}

/* ---------------------------------------------------------------- kneading */

/* Escape depth of the orbit of x0 = X0/G under f(x) = frac(1.5 x + a/G),
 * relative to the threshold T = thr/G:  the least n with x_n >= T, or -1 if
 * none within maxn steps (then *limited = 1).
 *
 * x_n = X/(G*2^n); the recursion is X' = (3X + a*2^{n+1}) mod (G*2^{n+1}).
 * Test x_n >= T  <=>  X >= thr*2^n. */
static long escape_depth(long a, long G, long thr, long X0, long maxn, int *limited)
{
  i128 X = X0, D = G, P = 1;            /* D = G*2^n, P = 2^n */
  *limited = 0;
  for (long n = 0; ; n++) {
    if (X >= (i128)thr * P) return n;
    if (n >= maxn) { *limited = 1; return -1; }
    if (5 * D > SAFE) { *limited = 2; return -1; }   /* precision exhausted */
    X = (3 * X + (i128)a * 2 * P) % (2 * D);
    D *= 2; P *= 2;
  }
}

/* ------------------------------------------------------------------ pruning */

typedef struct { i128 A, B; } iv;

typedef struct {
  long  depth;        /* deepest level actually computed                     */
  long  kill;         /* level at which S_k became empty, or -1              */
  long  comps;        /* components at the deepest level                     */
  double meas;        /* measure at the deepest level                        */
  double lambda;      /* growth rate of the component count over the tail    */
  int    stable;      /* component count constant over the tail window       */
  int    capped;      /* 1 if the interval cap was hit, 2 if precision ran out*/
  long  comps_at[256];
  double meas_at[256];
} prune_res;

#define TAIL 8

/* S_k for the window s = a/G, L = b/G, to at most `depth` levels.
 * cap = maximum number of components carried (no silent truncation: the run
 * stops and reports `capped`). */
static void prune(long a, long b, long G, long depth, long cap, prune_res *R)
{
  memset(R, 0, sizeof *R);
  R->kill = -1;
  if (depth > 250) depth = 250;

  iv *cur = malloc(sizeof(iv) * (size_t)cap);
  iv *nxt = malloc(sizeof(iv) * (size_t)cap);
  if (!cur || !nxt) { fprintf(stderr, "oom\n"); exit(1); }

  i128 D = G, ALPHA = a, THR = 2 * (i128)b;   /* level 0: D_0 = G */
  long n = 1;
  cur[0].A = 0; cur[0].B = THR;
  R->comps_at[0] = 1;
  R->meas_at[0] = (double)(2.0 * b / (double)G);

  for (long k = 0; k < depth; k++) {
    if (6 * D * 3 > SAFE) { R->capped = 2; R->depth = k; break; }
    i128 Dn = 3 * D, ALPHAn = 3 * ALPHA, THRn = 3 * THR;
    long m = 0;
    /* preimages, generated in increasing order: e outer, intervals inner */
    for (int e = 0; e <= 2; e++) {
      for (long t = 0; t < n; t++) {
        i128 A = 2 * (cur[t].A - ALPHA) + 2 * (i128)e * D;
        i128 B = 2 * (cur[t].B - ALPHA) + 2 * (i128)e * D;
        if (A < 0) A = 0;
        if (B > THRn) B = THRn;
        if (A >= B) continue;
        if (m && nxt[m-1].B >= A) {            /* merge touching/overlapping */
          if (nxt[m-1].B < B) nxt[m-1].B = B;
        } else {
          if (m >= cap) { R->capped = 1; break; }
          nxt[m].A = A; nxt[m].B = B; m++;
        }
      }
      if (R->capped == 1) break;
    }
    if (R->capped == 1) { R->depth = k; break; }

    iv *sw = cur; cur = nxt; nxt = sw;
    n = m; D = Dn; ALPHA = ALPHAn; THR = THRn;
    R->depth = k + 1;

    double meas = 0.0;
    for (long t = 0; t < n; t++) meas += (double)(cur[t].B - cur[t].A);
    meas /= (double)D;
    if (k + 1 < 256) { R->comps_at[k+1] = n; R->meas_at[k+1] = meas; }
    R->comps = n; R->meas = meas;

    if (n == 0) { R->kill = k + 1; break; }
  }

  /* tail diagnostics */
  long d = R->depth;
  if (R->kill < 0 && d >= TAIL && d < 256) {
    long c0 = R->comps_at[d - TAIL], c1 = R->comps_at[d];
    R->stable = 1;
    for (long k = d - TAIL; k <= d; k++)
      if (R->comps_at[k] != c1) { R->stable = 0; break; }
    R->lambda = (c0 > 0) ? pow((double)c1 / (double)c0, 1.0 / (double)TAIL) : 0.0;
  }
  free(cur); free(nxt);
}

/* verdict string */
static const char *verdict(const prune_res *R)
{
  if (R->kill >= 0)  return "KILL";
  if (R->capped == 1) return "CAP";
  if (R->capped == 2) return "PREC";
  if (R->stable)      return "FIN";
  return "FAT";
}

/* ------------------------------------------------------------------- modes */

static void mode_orbit(long a, long b, long G, long maxn)
{
  long thr = 2 * b;                       /* T = 2b/G */
  int lim0, limT;
  long e0 = escape_depth(a, G, thr, 0, maxn, &lim0);
  /* T^- maps to frac(beta*T + alpha) = frac((3b+a)/G) */
  long XT = (3 * b + a) % G;
  long eT = escape_depth(a, G, thr, XT, maxn, &limT);
  printf("# window s=%ld/%ld  L=%ld/%ld   alpha=%ld/%ld  T=2L=%ld/%ld\n",
         a, G, b, G, a, G, thr, G);
  printf("esc0 %ld  escT %ld  (limited: %d %d)\n", e0, eT, lim0, limT);
  /* print the orbit of 0 exactly, FLP-style */
  i128 X = 0, D = G, P = 1;
  char buf1[48], buf2[48];
  for (long n = 0; n <= (e0 >= 0 ? e0 : (maxn < 12 ? maxn : 12)); n++) {
    p128(buf1, X); p128(buf2, D);
    printf("  f^%ld(0) = %s/%s%s\n", n, buf1, buf2,
           (X >= (i128)thr * P) ? "   >= T : ESCAPE" : "");
    if (X >= (i128)thr * P) break;
    if (5 * D > SAFE) { printf("  (precision exhausted)\n"); break; }
    X = (3 * X + (i128)a * 2 * P) % (2 * D);
    D *= 2; P *= 2;
  }
}

static void mode_prune(long a, long b, long G, long depth)
{
  prune_res R;
  prune(a, b, G, depth, 1 << 22, &R);
  printf("# window s=%ld/%ld  L=%ld/%ld   J=[0,%ld/%ld)\n", a, G, b, G, 2*b, G);
  printf("# level  components  measure\n");
  for (long k = 0; k <= R.depth && k < 256; k++)
    printf("  %4ld  %10ld  %.12g\n", k, R.comps_at[k], R.meas_at[k]);
  int lim0, limT;
  long e0 = escape_depth(a, G, 2*b, 0, 100, &lim0);
  long eT = escape_depth(a, G, 2*b, (3*b+a) % G, 100, &limT);
  printf("verdict %s  kill %ld  depth %ld  comps %ld  meas %.6g  lambda %.6f  esc0 %ld escT %ld\n",
         verdict(&R), R.kill, R.depth, R.comps, R.meas, R.lambda, e0, eT);
}

/* X1: L = 1/3 (needs 3 | G), every position s = i/G with s + L <= 1. */
static void mode_x1(long G, long depth)
{
  if (G % 3) { fprintf(stderr, "x1 needs 3 | G\n"); exit(1); }
  long b = G / 3;
  printf("# X1  L = 1/3  G = %ld  depth = %ld\n", G, depth);
  printf("# i esc0 escT kill comps meas lambda verdict\n");
  long nkill = 0, nfin = 0, nfat = 0, ncap = 0, tot = 0;
  long maxesc = 0;
  for (long i = 0; i + b <= G; i++) {
    prune_res R;
    prune(i, b, G, depth, 1 << 16, &R);
    int lim0, limT;
    long e0 = escape_depth(i, G, 2*b, 0, 100, &lim0);
    long eT = escape_depth(i, G, 2*b, (3*b + i) % G, 100, &limT);
    const char *v = verdict(&R);
    printf("%ld %ld %ld %ld %ld %.6g %.4f %s\n",
           i, e0, eT, R.kill, R.comps, R.meas, R.lambda, v);
    tot++;
    if (!strcmp(v, "KILL")) nkill++;
    else if (!strcmp(v, "FIN")) nfin++;
    else if (!strcmp(v, "CAP") || !strcmp(v, "PREC")) ncap++;
    else nfat++;
    if (e0 > maxesc) maxesc = e0;
  }
  printf("# summary G=%ld positions=%ld KILL=%ld FIN=%ld FAT=%ld CAP=%ld maxesc0=%ld\n",
         G, tot, nkill, nfin, nfat, ncap, maxesc);
}

/* X2: the (position, length) map.  L = j/G for j in [jlo,jhi], s = i/G. */
static void mode_x2(long G, long jlo, long jhi, long depth)
{
  printf("# X2  G = %ld  L = j/G, j in [%ld,%ld]  depth = %ld\n", G, jlo, jhi, depth);
  printf("# j i esc0 escT kill comps meas lambda verdict\n");
  for (long j = jlo; j <= jhi; j++) {
    if (2 * j > G) { printf("# j=%ld skipped: L > 1/2\n", j); continue; }
    long nkill = 0, nfin = 0, nfat = 0, ncap = 0, tot = 0, nesc = 0;
    double lmin = 1e9, lmax = 0;
    for (long i = 0; i + j <= G; i++) {
      prune_res R;
      prune(i, j, G, depth, 1 << 15, &R);
      int lim0, limT;
      long e0 = escape_depth(i, G, 2*j, 0, 100, &lim0);
      long eT = escape_depth(i, G, 2*j, (3*j + i) % G, 100, &limT);
      const char *v = verdict(&R);
      printf("%ld %ld %ld %ld %ld %ld %.6g %.4f %s\n",
             j, i, e0, eT, R.kill, R.comps, R.meas, R.lambda, v);
      tot++;
      if (!strcmp(v, "KILL")) nkill++;
      else if (!strcmp(v, "FIN")) nfin++;
      else if (!strcmp(v, "CAP") || !strcmp(v, "PREC")) ncap++;
      else { nfat++; if (R.lambda < lmin) lmin = R.lambda;
                     if (R.lambda > lmax) lmax = R.lambda; }
      if (e0 >= 0 && eT >= 0) nesc++;
    }
    printf("# row j=%ld L=%.6f positions=%ld KILL=%ld FIN=%ld FAT=%ld CAP=%ld bothesc=%ld lambda[%.4f,%.4f]\n",
           j, (double)j / G, tot, nkill, nfin, nfat, ncap, nesc,
           (nfat ? lmin : 0.0), lmax);
    fflush(stdout);
  }
}

int main(int argc, char **argv)
{
  if (argc < 2) {
    fprintf(stderr,
      "usage: hold orbit|prune <a> <b> <G> [depth]\n"
      "       hold x1 <G> [depth]\n"
      "       hold x2 <G> <jlo> <jhi> [depth]\n");
    return 1;
  }
  if (!strcmp(argv[1], "orbit") && argc >= 5)
    mode_orbit(atol(argv[2]), atol(argv[3]), atol(argv[4]),
               argc > 5 ? atol(argv[5]) : 60);
  else if (!strcmp(argv[1], "prune") && argc >= 5)
    mode_prune(atol(argv[2]), atol(argv[3]), atol(argv[4]),
               argc > 5 ? atol(argv[5]) : 40);
  else if (!strcmp(argv[1], "x1") && argc >= 3)
    mode_x1(atol(argv[2]), argc > 3 ? atol(argv[3]) : 40);
  else if (!strcmp(argv[1], "x2") && argc >= 5)
    mode_x2(atol(argv[2]), atol(argv[3]), atol(argv[4]),
            argc > 5 ? atol(argv[5]) : 40);
  else { fprintf(stderr, "bad arguments\n"); return 1; }
  return 0;
}
