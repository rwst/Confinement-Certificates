#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# gencert.py -- plan-cert32 milestone M3: turn an engine verdict into a
# *kernel-checkable* Lean certificate.
#
# The engines of M2 (atlas.c, verify_atlas.py) decide emptiness numerically.
# This script re-runs the same exact pruning, but emits the funnel
#
#     T_0 = U  >=  T_1  >=  ...  >=  T_K = H (the blocks)
#
# as integer interval lists over ONE common denominator `D = Gden * p^K`,
# together with the two checks that `Z32/BlockCert.lean` proves sufficient:
#
#   (V2) for every I in T_k, every carry s in {-q+1,...,p-1} and every J in U,
#        the piece  { y in J : (p y - s)/q in I }  lies inside a SINGLE interval
#        of T_{k+1}                                        [funnelOk]
#   (V3) every block of T_K has at most one outgoing (carry, block) pair
#                                                          [funcOk]
#
# Both are pure integer arithmetic, so `decide` checks them in the kernel with
# no `native_decide` and no floating point anywhere in the chain.
#
#   ./gencert.py <Gden> <lo> <hi> [<lo> <hi> ...]      # auto-picks the depth K
#
# Three opt-in generalizations; `--pq` is milestone M6, the other two M4' P1:
#
#   --pq p q   work at the rational base p/q instead of the default 3/2, for any
#              coprime p > q > 1.  The carry alphabet is {-q+1,...,p-1}, exactly
#              p+q-1 letters (4 at (3,2), 6 at (4,3)); the branch-s preimage of
#              [a,b] is [(qa+s)/p, (qb+s)/p]; the common denominator is G*p^K.
#              NOTHING else changes -- in particular the soundness theorem
#              `Z32.BlockCert.Cert.not_confined` is proved for all such (p,q),
#              because the aperiodicity of the carry word it contradicts
#              (`Z32.not_isEventuallyPeriodic_carry`) is.
#
#   --closed   the intervals are CLOSED on the right, [lo/G, hi/G].  Emptiness
#              of a closed set is a STRONGER statement than emptiness of its
#              half-open shadow, and the literature is often printed closed
#              ([Dub08] Cor 1.2).  Every comparison flips accordingly: a piece
#              is empty iff hi < lo (not hi <= lo), and two intervals meet iff
#              max(lo) <= min(hi) (not <).
#   --ranked   emit a RANK-STRATIFIED block graph instead of a functional one.
#              The blocks are then the raw components of the final level (no
#              hull merging), each carrying a rank, and the check is
#                  rank(successor) <= rank(block),  and
#                  at most one successor of EQUAL rank.
#              An infinite path has non-increasing rank, hence eventually
#              constant rank, hence is eventually deterministic -- which is all
#              the soundness proof needs.  `strata := []` (every rank 0) is the
#              old "at most one outgoing edge" condition verbatim.
#
# Convention note: this file's carry is [Dub09AA]'s  s_n = q x_{n+1} - p x_n,
# i.e. the NEGATIVE of the `e` printed by atlas.c, so that it matches
# `Z32.carry` and `Z32.not_isEventuallyPeriodic_carry` verbatim.

import sys
from fractions import Fraction as F

P, Q = 3, 2              # the base p/q; set by --pq
CARRIES = (-1, 0, 1, 2)  # {-q+1, ..., p-1}; recomputed by --pq
CLOSED = False           # set by --closed


def nonempty(a, b):
    """Is the interval from `a` to `b` nonempty, under the active convention?"""
    return a <= b if CLOSED else a < b


def meets(cA, cB, lo, hi):
    """Do [cA,cB] and [lo,hi] intersect, under the active convention?"""
    return (cB >= lo and cA <= hi) if CLOSED else (cB > lo and cA < hi)


def merge(iv):
    """Sort and coalesce a list of intervals."""
    out = []
    for a, b in sorted(iv):
        if not nonempty(a, b):
            continue
        if out and out[-1][1] >= a:
            if out[-1][1] < b:
                out[-1] = (out[-1][0], b)
        else:
            out.append((a, b))
    return out


def preimage_piece(I, s, J):
    """{ y in J : (p y - s)/q in I }, as an interval (possibly empty)."""
    a, b = I
    lo, hi = (Q * a + s) / F(P), (Q * b + s) / F(P)
    return (max(lo, J[0]), min(hi, J[1]))


def prune(S, U):
    """U cap f^{-1}(S)."""
    out = []
    for I in S:
        for s in CARRIES:
            for J in U:
                x, y = preimage_piece(I, s, J)
                if nonempty(x, y):
                    out.append((x, y))
    return merge(out)


def blocks_fixpoint(S):
    """Coalesce components into consecutive-run blocks until the block-hull
    transition relation is a partial function.  Same routine as
    verify_atlas.py, restated on hulls."""
    blk = [[c] for c in S]
    while True:
        hulls = [(b[0][0], b[-1][1]) for b in blk]
        changed = False
        for (hA, hB) in hulls:
            for s in CARRIES:
                lo, hi = (P * hA - s) / F(Q), (P * hB - s) / F(Q)
                hit = [j for j, (cA, cB) in enumerate(hulls) if meets(cA, cB, lo, hi)]
                if len(hit) >= 2:
                    lo_i, hi_i = hit[0], hit[-1]
                    blk = (blk[:lo_i] + [sum(blk[lo_i:hi_i + 1], [])]
                           + blk[hi_i + 1:])
                    changed = True
                    break
            if changed:
                break
        if not changed:
            return [(b[0][0], b[-1][1]) for b in blk]


def outdeg(H):
    """max over blocks of #{(s,j) : image of H_i under s meets H_j}."""
    m = 0
    for (hA, hB) in H:
        d = 0
        for s in CARRIES:
            lo, hi = (P * hA - s) / F(Q), (P * hB - s) / F(Q)
            d += sum(1 for (cA, cB) in H if meets(cA, cB, lo, hi))
        m = max(m, d)
    return m


# ---------------------------------------------------------------- integer view

def scale(iv, D):
    out = []
    for a, b in iv:
        na, nb = a * D, b * D
        assert na.denominator == 1 and nb.denominator == 1, (a, b, D)
        out.append((int(na), int(nb)))
    return out


def check_v2(D, U, cur, nxt):
    """(V2), verbatim as `Z32.BlockCert.levelOk` will read it, over ZZ."""
    for I in cur:
        for s in CARRIES:
            for J in U:
                lo = max(Q * I[0] + s * D, P * J[0])
                hi = min(Q * I[1] + s * D, P * J[1])
                if not nonempty(lo, hi):
                    continue
                if not any(P * K[0] <= lo and hi <= P * K[1] for K in nxt):
                    return False, (I, s, J, lo, hi)
    return True, None


def out_edges(D, H, i):
    """Indices reachable from block `i`, verbatim as `Z32.BlockCert.outEdges`."""
    I = H[i]
    return [(s, j) for s in CARRIES for j, J in enumerate(H)
            if nonempty(max(P * I[0], Q * J[0] + s * D), min(P * I[1], Q * J[1] + s * D))]


def check_v3(D, H, rank=None):
    """(V3), verbatim as `Z32.BlockCert.funcOk` will read it, over ZZ.  With
    `rank = None` every block gets rank 0, which is the plain "at most one
    outgoing edge" condition."""
    r = rank if rank is not None else [0] * len(H)
    for i in range(len(H)):
        edges = out_edges(D, H, i)
        if any(r[j] > r[i] for (_, j) in edges):
            return False, (H[i], "rank increases", edges)
        if sum(1 for (_, j) in edges if r[j] == r[i]) > 1:
            return False, (H[i], "two same-rank successors", edges)
    return True, None


# ------------------------------------------------------- rank stratification

def tarjan(n, adj):
    """SCCs, in reverse topological order.  Iterative (levels can be deep)."""
    index = [None] * n
    low = [0] * n
    on = [False] * n
    stack, out, ctr = [], [], 0
    for root in range(n):
        if index[root] is not None:
            continue
        work = [(root, 0)]
        while work:
            v, pi = work[-1]
            if pi == 0:
                index[v] = low[v] = ctr
                ctr += 1
                stack.append(v)
                on[v] = True
            recurse = False
            for i in range(pi, len(adj[v])):
                w = adj[v][i]
                if index[w] is None:
                    work[-1] = (v, i + 1)
                    work.append((w, 0))
                    recurse = True
                    break
                if on[w]:
                    low[v] = min(low[v], index[w])
            if recurse:
                continue
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on[w] = False
                    comp.append(w)
                    if w == v:
                        break
                out.append(comp)
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
    return out


def ranks_of(D, H):
    """Rank every block by its longest path in the condensation (sinks = 0), so
    that inter-SCC edges strictly drop the rank and intra-SCC edges preserve it.
    Returns None if some block still has two successors of its own rank -- i.e.
    if some SCC is not a simple cycle, the one thing this certificate cannot
    tolerate."""
    n = len(H)
    E = [(i, s, j) for i in range(n) for (s, j) in out_edges(D, H, i)]
    adj = [[] for _ in range(n)]
    for (i, _, j) in E:
        adj[i].append(j)
    comps = tarjan(n, adj)
    cid = [0] * n
    for ci, comp in enumerate(comps):
        for v in comp:
            cid[v] = ci
    cadj = [set() for _ in comps]
    for (i, _, j) in E:
        if cid[i] != cid[j]:
            cadj[cid[i]].add(cid[j])
    lp = [None] * len(comps)
    for c in range(len(comps)):          # Tarjan order: successors come first
        lp[c] = max((lp[d] + 1 for d in cadj[c]), default=0)
    rank = [lp[cid[v]] for v in range(n)]
    ok, why = check_v3(D, H, rank)
    return rank if ok else None


# ---------------------------------------------------------------------- driver

def lean_list(iv):
    return "[" + ", ".join(f"({a}, {b})" for a, b in iv) + "]"


def main():
    global CLOSED, P, Q, CARRIES
    argv = sys.argv[1:]
    name = None
    if "--lean" in argv:
        i = argv.index("--lean")
        name = argv[i + 1]
        argv = argv[:i] + argv[i + 2:]
    if "--pq" in argv:
        i = argv.index("--pq")
        P, Q = int(argv[i + 1]), int(argv[i + 2])
        argv = argv[:i] + argv[i + 3:]
        if not (1 < Q < P):
            print(f"# refusing (p,q) = ({P},{Q}): need p > q > 1")
            return 1
        from math import gcd
        if gcd(P, Q) != 1:
            print(f"# refusing (p,q) = ({P},{Q}): need p, q coprime")
            return 1
        CARRIES = tuple(range(-Q + 1, P))
    ranked = "--ranked" in argv
    argv = [a for a in argv if a != "--ranked"]
    CLOSED = "--closed" in argv
    argv = [a for a in argv if a != "--closed"]
    br = "]" if CLOSED else ")"
    G = int(argv[0])
    nums = [int(x) for x in argv[1:]]
    U = [(F(nums[i], G), F(nums[i + 1], G)) for i in range(0, len(nums), 2)]
    if (P, Q) != (3, 2):
        print(f"# base p/q = {P}/{Q}, carries {list(CARRIES)}"
              f"{'  (p > q^2: [Dub09AA] section 4 calls this regime open)' if P > Q * Q else ''}")
    print("# U =", " ".join(f"[{a},{b}{br}" for a, b in U),
          " |U| =", float(sum(b - a for a, b in U)))

    levels = [U]
    K, rank = None, None
    for k in range(1, 61):
        S = prune(levels[-1], U)
        levels.append(S)
        if not S:
            print(f"# KILL at depth {k}")
            K = k
            break
        if ranked:
            # blocks = the raw components; no hull merging, so (V2) is automatic
            # and only the rank condition can fail.
            r = ranks_of(G * P ** k, scale(S, G * P ** k))
            print(f"# level {k:3d}: {len(S):5d} components, "
                  f"{'ranked ' + str(max(r) + 1) + ' strata' if r else 'not rankable'}")
            if r is not None:
                K, rank = k, r
                break
            continue
        H = blocks_fixpoint(S)
        print(f"# level {k:3d}: {len(S):5d} components, {len(H):5d} blocks, "
              f"outdeg {outdeg(H)}")
        if outdeg(H) <= 1:
            levels[-1] = S            # keep the exact level for the chain check
            K = k
            break
    if K is None:
        print("# no certificate found within depth 60")
        return 1

    if ranked:
        chain = levels[:K + 1]         # every level exact; blocks = T_K
    else:
        Hb = blocks_fixpoint(levels[K]) if levels[K] else []
        chain = levels[:K] + [Hb]      # T_0..T_{K-1} exact, T_K = the blocks
    D = G * P ** K
    ichain = [scale(t, D) for t in chain]
    iU = ichain[0]

    for k in range(K):
        ok, why = check_v2(D, iU, ichain[k], ichain[k + 1])
        if not ok:
            print("# (V2) FAILED at level", k, why)
            return 1
    ok, why = check_v3(D, ichain[K], rank)
    if not ok:
        print("# (V3) FAILED", why)
        return 1
    strata = []
    if rank is not None:
        strata = [[ichain[K][i] for i in range(len(rank)) if rank[i] == r]
                  for r in range(max(rank) + 1)]
    print(f"# (V2) and (V3) verified over ZZ at D = {G}*{P}^{K} = {D}")
    if rank is not None:
        print(f"# rank strata (lowest first): {[len(t) for t in strata]}")
    print(f"# funnel sizes: {[len(t) for t in ichain]}")
    print(f"# largest integer: {max(abs(x) for t in ichain for I in t for x in I)}")

    print()
    if name is None:
        print(f"  D := {D}")
        print(f"  U := {lean_list(iU)}")
        print("  levels :=")
        for t in ichain[1:]:
            print(f"    {lean_list(t)},")
        return 0

    total = sum(b - a for a, b in U)
    disp = " u ".join(f"[{nums[i]}/{G},{nums[i+1]}/{G}{br}" for i in range(0, len(nums), 2))
    flags = ("".join(f" {f}" for f in
                     ([f"--pq {P} {Q}"] if (P, Q) != (3, 2) else [])
                     + (["--closed"] if CLOSED else [])
                     + (["--ranked"] if ranked else [])))
    print(f"/-- Certificate for `{disp}`, total length `{total}`; "
          f"funnel depth {K}, {len(ichain[K])} block(s)"
          f"{' in ' + str(len(strata)) + ' rank strata' if strata else ''}.  Generated by "
          f"`Z32/gencert.py{flags} {G} {' '.join(str(x) for x in nums)}`. -/")
    print(f"def {name} : Cert where")
    print(f"  D := {D}")
    if (P, Q) != (3, 2):
        print(f"  p := {P}")
        print(f"  q := {Q}")
    if CLOSED:
        print("  closed := true")
    print(f"  U := {lean_list(iU)}")
    print("  levels := [")
    for i, t in enumerate(ichain[1:]):
        sep = "]" if i == len(ichain) - 2 else ","
        print(f"    {lean_list(t)}{sep}")
    if strata:
        print("  strata := [")
        for i, t in enumerate(strata):
            sep = "]" if i == len(strata) - 1 else ","
            print(f"    {lean_list(t)}{sep}")
    print()
    print(f"@[category API, AMS 11 37, ref \"Dub09AA\", group \"z32_block_cert\"]")
    print(f"theorem {name}_ok : {name}.ok = true := by decide")
    return 0


if __name__ == "__main__":
    sys.exit(main())
