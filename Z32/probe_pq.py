#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# probe_pq.py -- plan-cert32 milestone M6/M7 feasibility probe.
#
# The M2/M3 engines are hardwired to p/q = 3/2.  Before parameterizing them
# (milestone M6) this script answers, exactly and cheaply, the one question
# that decides whether a target is worth the engineering: is the *archimedean
# hold set* of U non-trivial at (p,q)?
#
#     y_{n+1} = (p y_n - s)/q,   s in {-q+1, ..., p-1}   (p+q-1 carries)
#     branch-s preimage of [a,b) is [(q a + s)/p, (q b + s)/p)
#     S_0 = U,  S_{k+1} = U cap f^{-1}(S_k)
#
# All arithmetic is `fractions.Fraction`: no floating point in any decision.
# Three verdicts, matching the engines' vocabulary:
#
#   KILL       S_k = {} at some depth  -- emptiness, no theory needed
#   INVARIANT  S_1 = U  -- the pruning removes NOTHING, so no hold-set-only
#              certificate (KILL or CYCLE) can ever apply to U.  This is a
#              stronger no-go than the (3,2) band's cycle count: there the
#              obstruction is a count, here it is exact invariance.
#   shrinking  the interesting case: measure -> 0 with a bounded component
#              count, i.e. the CYCLE-certifiable shape
#
# Results as of 2026-07-27 are quoted in plans/plan-cert32.html sections 11.2
# and 11.3.  The headline is (a): [Aki08] Conjecture 1.4's set is INVARIANT.
from fractions import Fraction as F

CAP = 4000          # component cap; above this we report FAT and stop


def step(S, U, p, q):
    """One pruning step, exactly."""
    out = []
    for a, b in S:
        for s in range(-q + 1, p):
            lo, hi = F(q * a + s, p), F(q * b + s, p)
            for c, d in U:
                x, y = max(lo, c), min(hi, d)
                if x < y:
                    out.append((x, y))
    if not out:
        return []
    out.sort()
    m = [out[0]]
    for a, b in out[1:]:
        if a <= m[-1][1]:
            m[-1] = (m[-1][0], max(m[-1][1], b))
        else:
            m.append((a, b))
    return m


def hold(U, p, q, depth=30):
    S = sorted(U)
    for k in range(1, depth + 1):
        T = step(S, U, p, q)
        if not T:
            return f"KILL at depth {k}"
        if T == S:
            return (f"INVARIANT: hold set = U itself, {len(S)} comp, "
                    f"measure {float(sum(b - a for a, b in S)):.6f}")
        if len(T) > CAP:
            return f"FAT: >{CAP} components by depth {k}"
        S = T
    return (f"shrinking at depth {depth}: {len(S)} comp, "
            f"measure {float(sum(b - a for a, b in S)):.8f}")


def rep(U, p, q, label, depth=30):
    print(f"  {label:40s} {hold(U, p, q, depth)}", flush=True)


if __name__ == "__main__":
    print("(a) two-cell sets [0,c) u [1-c,1) at (4,3); c = 1/4 IS [Aki08] Conj 1.4:")
    for c in (F(1, 4), F(23, 100), F(11, 50), F(1, 5), F(3, 20), F(1, 8)):
        rep([(F(0), c), (F(1) - c, F(1))], 4, 3, f"c = {c} = {float(c):.5f}")

    print("\n(b) the (3,2) analogue; [Dub10] proves c = 1/3 NONEMPTY:")
    for c in (F(1, 3), F(3, 10), F(1, 4), F(1, 5)):
        rep([(F(0), c), (F(1) - c, F(1))], 3, 2, f"c = {c} = {float(c):.5f}")

    print("\n(c) p > q^2, where [Aki08] Thm 2.5 builds nonempty Cantor sets:")
    rep([(F(0), F(1, 5)), (F(4, 5), F(1))], 5, 2, "(5,2) two-cell c = 1/5")

    print("\n(d) [Dub09AA] zone q < p < q^2: every window of length 1/p resolves:")
    for (p, q) in ((4, 3), (5, 3), (5, 4), (7, 5)):
        bad = sum(1 for i in range(8)
                  if hold([(F(i, 8), F(i, 8) + F(1, p))], p, q, 25)
                  .startswith(("FAT", "INVARIANT")))
        print(f"  (p,q)=({p},{q}): {q}<{p}<{q * q};  8 windows, unresolved: {bad}",
              flush=True)

    print("\n(e) p > q^2 -- [Dub09AA] section 4 calls this regime wholly open:")
    for (p, q) in ((5, 2), (7, 2), (9, 2), (10, 3)):
        print(f"  (p,q)=({p},{q}), q^2={q * q} < p:", flush=True)
        for i in range(6):
            s = F(i, 6)
            print(f"    s={str(s):5s}: {hold([(s, s + F(1, p))], p, q)}", flush=True)
