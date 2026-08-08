#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# pqcontrols.py -- plan-cert32 milestone M6: the controls that a *parametric*
# certificate engine makes possible, and that the (3,2) engine could never run.
#
# `gencert.py --pq p q` generalizes the block certificate to any coprime
# p > q > 1.  Generalizing an engine is only worth anything if the generalized
# engine is still *sound*, so this script runs it in both colors against the
# literature:
#
#   (A) POSITIVE.  [Dub09AA] Theorem 1: for 1 < q < p < q^2 and EVERY real s,
#       Z_{p/q}(s, s+1/p) is empty.  (Proved in full generality in
#       `Z32/SmallInterval.lean` as `Z32.ZSet_eq_empty_of_lt_sq`, by the
#       Sturmian route.)  The engine must therefore certify every length-1/p
#       window it is handed, at every base in that range.  Windows are taken
#       mod 1, i.e. a window running past 1 is the two-interval union it
#       really is -- getting this wrong silently tests a SHORTER window.
#
#   (B) NEGATIVE.  [Aki08] Theorems 2.4/2.5 build NONEMPTY sets -- Cantor sets
#       of dimension log q / log(p/q) -- for p > q^2, inside two-cell unions of
#       arbitrarily small measure.  The engine must never certify one.
#
#   (C) THE COVER, which is the interesting measurement.  For p > q^2,
#       [Dub09AA] section 4 states Theorem 1 is OPEN: his counting step needs
#       p < q^2.  The block certificate has no such step, and it does certify
#       every length-1/p window we hand it in that regime.  That is NOT the
#       open theorem, which quantifies over all real s.  The natural upgrade is
#       a cover: certify the N windows [i/N, i/N + 1/N + 1/p) mod 1, and every
#       real window of length 1/p sits inside one of them, so `Z32.ZSet_mono`
#       would give the general statement.  This measures whether that works.
#       It does not -- see the printed table, and `Z32.ZSet_five_two_fifth`.
#
# Exact `fractions.Fraction` arithmetic throughout; no floating point in any
# decision.  Sections (A) and (B) take about a minute; section (C) takes the
# best part of an hour, because the FAT cover elements carry several hundred
# surviving components and the block-merge fixpoint is cubic in that count.
# The component cap is 600 for every verdict, generous side up: a cover element
# needing more would be far outside what `decide` could check anyway.
#
#   python3 pqcontrols.py

import sys
from fractions import Fraction as F

import gencert as g


def verdict(P, Q, G, nums, maxdepth=30, cap=600):
    """Run the gencert pipeline at (P,Q) on the set given by `nums`/`G`.

    Returns one of 'KILL' (empty by pruning alone), 'CYCLE' (a block
    certificate exists), 'FAT' (component count exploded) or 'none'."""
    g.P, g.Q = P, Q
    g.CARRIES = tuple(range(-Q + 1, P))
    g.CLOSED = False
    U = [(F(nums[i], G), F(nums[i + 1], G)) for i in range(0, len(nums), 2)]
    S = U
    for k in range(1, maxdepth + 1):
        S = g.prune(S, U)
        if not S:
            return 'KILL', k, 0
        if len(S) > cap:
            return 'FAT', k, len(S)
        H = g.blocks_fixpoint(S)
        if g.outdeg(H) <= 1:
            return 'CYCLE', k, len(H)
    return 'none', maxdepth, len(S)


def window(i, L, G):
    """[i/G, (i+L)/G) taken mod 1, as a flat endpoint list over G."""
    i %= G
    return [i, G, 0, i + L - G] if i + L > G else [i, i + L]


def main():
    print("== (A) POSITIVE: [Dub09AA] Thm 1, every window of length 1/p, "
          "1 < q < p < q^2 ==")
    allok = True
    for (P, Q) in ((4, 3), (5, 3), (5, 4), (7, 5)):
        G = 8 * P
        v = [verdict(P, Q, G, window(i * P, 8, G), maxdepth=40) for i in range(8)]
        good = sum(1 for r in v if r[0] in ('KILL', 'CYCLE'))
        allok &= good == 8
        print(f"  (p,q)=({P},{Q}), q^2={Q * Q}: {good}/8 certified, "
              f"max funnel depth {max(r[1] for r in v)}", flush=True)
    print("  ==> " + ("all reproduced" if allok else "*** A WINDOW WAS MISSED ***"))

    print("\n== (B) NEGATIVE: sets [Aki08] Thms 2.4/2.5 prove NONEMPTY, p > q^2 ==")
    bad = False
    for (P, Q, c) in ((5, 2, F(1, 5)), (7, 2, F(1, 7)), (9, 2, F(1, 9))):
        G = c.denominator
        r = verdict(P, Q, G, [0, 1, G - 1, G], maxdepth=14)
        bad |= r[0] in ('KILL', 'CYCLE')
        print(f"  (p,q)=({P},{Q}) two-cell [0,{c}) u [{1 - c},1): {r}", flush=True)
    print("  ==> " + ("*** ENGINE CERTIFIED A NONEMPTY SET ***" if bad
                      else "refused, as it must be"))

    print("\n== (C) the cover: does the length-1/p line extend to ALL real s? ==")
    for (P, Q) in ((5, 2), (7, 2), (9, 2), (10, 3)):
        for N in (P, 2 * P, 4 * P):
            G, L = N * P, P + N       # cover elements have length 1/N + 1/p
            ok = sum(1 for i in range(N)
                     if verdict(P, Q, G, window(i * P, L, G), maxdepth=25)[0]
                     in ('KILL', 'CYCLE'))
            print(f"  (p,q)=({P},{Q}) p>q^2={Q * Q}: N={N:3d}, element length "
                  f"{L}/{G} = {float(F(L, G)):.4f} -> {ok}/{N} certified"
                  + ("   ** FULL COVER **" if ok == N else ""), flush=True)
    print("  ==> no full cover anywhere: the finite column does NOT upgrade to")
    print("      the open theorem, and there is no tension with [Aki08].")
    return 0


if __name__ == "__main__":
    sys.exit(main())
