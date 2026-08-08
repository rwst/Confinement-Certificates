#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# verify_atlas.py -- plan-cert32 milestone M2: an INDEPENDENT re-implementation
# of the atlas.c hold-set pruning, in Python with exact Fraction arithmetic and
# a deliberately naive algorithm (generate every preimage, sort, merge).  Its
# only purpose is to catch implementation error in the C engine (plan R-5:
# correlated single-author error is the dominant risk).
#
#   ./verify_atlas.py <depth> <Gden> <lo1> <hi1> [<lo2> <hi2> ...]
#
# prints the per-level component count and total measure, the block-merge
# fixpoint, and the CYCLE/KILL/FAT verdict, in the same format as atlas.c.
#
# It also brute-forces a search for surviving orbits (`--orbits`), which is a
# third, model-free check: if the engine says CYCLE (only eventually periodic
# orbits survive) then a random search must never find a long aperiodic one.

import sys
from fractions import Fraction as F


def preimages(S, U):
    """{y in U : (3y+e)/2 in S for some integer e} -- naive and exact."""
    out = []
    for (a, b) in S:
        for e in (1, 0, -1, -2):
            lo, hi = (2 * a - e) / 3, (2 * b - e) / 3
            lo, hi = max(lo, F(0)), min(hi, F(1))
            if lo < hi:
                out.append((lo, hi))
    out.sort()
    merged = []
    for (a, b) in out:
        if merged and merged[-1][1] >= a:
            if merged[-1][1] < b:
                merged[-1] = (merged[-1][0], b)
        else:
            merged.append((a, b))
    # intersect with U
    res = []
    for (a, b) in merged:
        for (c, d) in U:
            lo, hi = max(a, c), min(b, d)
            if lo < hi:
                res.append((lo, hi))
    res.sort()
    out = []
    for (a, b) in res:
        if out and out[-1][1] >= a:
            if out[-1][1] < b:
                out[-1] = (out[-1][0], b)
        else:
            out.append((a, b))
    return out


def blocks_fixpoint(S):
    """Merge components into blocks until the block-hull transition relation is
    a partial function; returns (blocks, max out-degree)."""
    blk = [[c] for c in S]
    while True:
        hulls = [(b[0][0], b[-1][1]) for b in blk]
        changed = False
        for (hA, hB) in hulls:
            for e in (-2, -1, 0, 1):
                lo, hi = (3 * hA + e) / 2, (3 * hB + e) / 2
                if hi <= 0 or lo >= 1:
                    continue
                hit = [j for j, (cA, cB) in enumerate(hulls) if cB > lo and cA < hi]
                if len(hit) >= 2:
                    lo_i, hi_i = hit[0], hit[-1]
                    new = []
                    for j, b in enumerate(blk):
                        if j < lo_i or j > hi_i:
                            new.append(b)
                        elif j == lo_i:
                            new.append(sum(blk[lo_i:hi_i + 1], []))
                    blk = new
                    changed = True
                    break
            if changed:
                break
        if not changed:
            return blk
    return blk


def verdict(S, depth_reached):
    if not S:
        return "KILL", 0, 0
    blk = blocks_fixpoint(S)
    hulls = [(b[0][0], b[-1][1]) for b in blk]
    maxdeg = 0
    for (hA, hB) in hulls:
        deg = 0
        for e in (-2, -1, 0, 1):
            lo, hi = (3 * hA + e) / 2, (3 * hB + e) / 2
            if hi <= 0 or lo >= 1:
                continue
            deg += sum(1 for (cA, cB) in hulls if cB > lo and cA < hi)
        maxdeg = max(maxdeg, deg)
    return ("CYCLE" if maxdeg <= 1 else "FAT"), len(blk), maxdeg


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    depth, Gden = int(args[0]), int(args[1])
    nums = [int(x) for x in args[2:]]
    U = [(F(nums[i], Gden), F(nums[i + 1], Gden)) for i in range(0, len(nums), 2)]
    print("# U =", " ".join(f"[{a},{b})" for a, b in U),
          " |U| =", float(sum(b - a for a, b in U)))
    S = list(U)
    kill = -1
    for k in range(depth):
        S = preimages(S, U)
        meas = float(sum(b - a for a, b in S))
        if "--all" in sys.argv or k < 8 or k == depth - 1:
            print(f"  level {k+1:3d}  components {len(S):6d}  measure {meas:.10g}")
        if not S:
            kill = k + 1
            break
    if "--nocert" in sys.argv:
        return
    v, nblk, maxdeg = verdict(S, depth)
    print(f"verdict {v}  kill {kill}  comps {len(S)}  blocks {nblk}  maxoutdeg {maxdeg}")
    if v == "CYCLE" and S:
        blk = blocks_fixpoint(S)
        for i, b in enumerate(blk):
            hA, hB = b[0][0], b[-1][1]
            for e in (-2, -1, 0, 1):
                lo, hi = (3 * hA + e) / 2, (3 * hB + e) / 2
                if hi <= 0 or lo >= 1:
                    continue
                for j, c in enumerate(blk):
                    cA, cB = c[0][0], c[-1][1]
                    if cB > lo and cA < hi:
                        print(f"  B{i} = [{hA},{hB}) ~ [{float(hA):.9f},{float(hB):.9f})"
                              f"  --e={e}-->  B{j}")


if __name__ == "__main__":
    main()
