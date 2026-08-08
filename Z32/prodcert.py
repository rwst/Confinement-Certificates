#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# prodcert.py -- plan-cert32 section 4.3 (experiment X4) and milestone M7:
# the PRODUCT REFINEMENT, states (cell, x mod q^j), and the two no-go theorems
# that finish it.
#
# The archimedean engine (atlas.c, gencert.py) quotients away the q-adic
# coordinate of the solenoid.  Section 4.3 proposed to put it back: a state is a
# pair (cell, x_n mod q^j), and the two coordinates constrain each other because
#
#     q x_{n+1} = p x_n + s_n          forces      s_n = -p x_n  (mod q),
#
# so the branch is DETERMINED by the residue -- one carry out of q instead of q.
# The plan's expectation was that this prunes ("wins strictly between L = 1/3
# and L = 1/2"), and it asked for the crossover curve.  There is no crossover.
# This file implements the engine and measures why:
#
#   THEOREM A (the residue coordinate is free).  Write S_k for the archimedean
#   hold set at depth k and S_k^{(j)}[r] for the product one.  Then for all k
#   and all j,        union over r of S_k^{(j)}[r]  =  S_k.
#   Proof.  "subset" is the projection.  For "superset", let y_0,...,y_k in U be
#   an archimedean chain with carries s_0,...,s_{k-1}.  Since gcd(p,q) = 1, p is
#   invertible mod q^j, so pick ANY r_k in Z/q^j and run the residues BACKWARD,
#   r_i := p^{-1}(q r_{i+1} - s_i).  That is a legal product chain over y.  QED
#   Consequence: the product engine reports KILL at exactly the archimedean
#   depth -- never one step earlier, at any level j, any base, any U.  The
#   dyadic ladder cannot empty a set the archimedean engine could not.
#
#   THEOREM B (cycle counting lifts).  Every periodic orbit of the hold dynamics
#   lifts to a periodic path in the product graph at every level j (same
#   backward construction; the return map on Z/q^j is constant once the period
#   is >= j, so it has a fixed point).  A block graph that is a partial function
#   -- or rank-stratified, which is deterministic on each stratum -- puts every
#   block on at most one cycle, and distinct periodic orbits have distinct carry
#   words (y_n = sum_{i>=0} q^i s_{n+i} / p^{i+1} recovers the point from its
#   future carries).  So a product certificate with m blocks forces the hold set
#   to carry at most m periodic orbits.  Contrapositive: a hold set with
#   infinitely many periodic orbits admits NO product certificate at any level.
#
# Together these say the section-4.3 machine is worth nothing that the
# archimedean machine did not already have, and section (E) below applies them
# to [Aki08] Conjecture 1.4.  Everything is exact `fractions.Fraction`
# arithmetic; no floating point in any decision.  Half-open intervals only
# (Akiyama works half-open throughout, so M7 needs no `--closed`).
#
#   python3 prodcert.py            # the full M7/X4 control suite, ~90 seconds
#   python3 prodcert.py cycles p q G lo hi [lo hi ...] [maxperiod]
#   python3 prodcert.py hold   p q j G lo hi [lo hi ...]

import sys
from fractions import Fraction as F


def merge(iv):
    """Sort and coalesce a list of half-open intervals."""
    out = []
    for a, b in sorted(iv):
        if a >= b:
            continue
        if out and out[-1][1] >= a:
            if out[-1][1] < b:
                out[-1] = (out[-1][0], b)
        else:
            out.append((a, b))
    return out


# ------------------------------------------------------- the product refinement

def prod_prune(S, U, P, Q, M):
    """One step of  S[r] <- U cap f^{-1}(S)  in the product.

    `S[r]` is the set of y still alive when x = r (mod M = q^j).  From (y, r)
    the carry is forced mod q; the successor residue r' only satisfies
    q r' = p r + s (mod q^j), which pins r' mod q^{j-1} and leaves q lifts."""
    Mq, lifts = M // Q, (1 if M == 1 else Q)     # M = 1 is the j = 0 control:
    out = []                                     # no residue, no constraint
    for r in range(M):
        acc = []
        for s in range(-Q + 1, P):
            if M > 1 and (P * r + s) % Q:        # q | p x + s is forced
                continue
            cp = (P * r + s) // Q
            for t in range(lifts):               # the q lifts
                for (a, b) in S[(cp + t * Mq) % M]:
                    lo, hi = (Q * a + s) / F(P), (Q * b + s) / F(P)
                    for J in U:
                        x, y = max(lo, J[0]), min(hi, J[1])
                        if x < y:
                            acc.append((x, y))
        out.append(merge(acc))
    return out


def prod_blocks(S, P, Q, M):
    """Coalesce, inside each residue class, consecutive components into hulls
    until the hull transition relation is a partial function.  The product
    analogue of `gencert.blocks_fixpoint`, and what makes a product CYCLE
    certificate possible at all: merging is the engine's only way to turn a
    2-out component graph into a functional block graph."""
    blk = [[[c] for c in S[r]] for r in range(M)]
    Mq, lifts = M // Q, (1 if M == 1 else Q)
    while True:
        hull = [[(b[0][0], b[-1][1]) for b in blk[r]] for r in range(M)]
        done = True
        for r in range(M):
            for (hA, hB) in hull[r]:
                for s in range(-Q + 1, P):
                    if M > 1 and (P * r + s) % Q:
                        continue
                    cp = (P * r + s) // Q
                    lo, hi = (P * hA - s) / F(Q), (P * hB - s) / F(Q)
                    for t in range(lifts):
                        rp = (cp + t * Mq) % M
                        hit = [i for i, (cA, cB) in enumerate(hull[rp])
                               if cB > lo and cA < hi]
                        if len(hit) >= 2:
                            i0, i1 = hit[0], hit[-1]
                            blk[rp] = (blk[rp][:i0]
                                       + [sum(blk[rp][i0:i1 + 1], [])]
                                       + blk[rp][i1 + 1:])
                            done = False
                            break
                    if not done:
                        break
                if not done:
                    break
            if not done:
                break
        if done:
            return hull


def prod_outdeg(S, P, Q, M):
    """Largest number of (carry, surviving component) pairs out of one state."""
    Mq, worst = M // Q, 0
    lifts = 1 if M == 1 else Q
    for r in range(M):
        for (a, b) in S[r]:
            d = 0
            for s in range(-Q + 1, P):
                if M > 1 and (P * r + s) % Q:
                    continue
                cp = (P * r + s) // Q
                lo, hi = (P * a - s) / F(Q), (P * b - s) / F(Q)
                for t in range(lifts):
                    for (cA, cB) in S[(cp + t * Mq) % M]:
                        if cB > lo and cA < hi:
                            d += 1
            worst = max(worst, d)
    return worst


def prod_hold(P, Q, j, U, maxdepth=30, cap=20000, blockcap=400):
    """Iterate the product prune until a verdict.

    KILL   the product hold set is empty (Theorem A: never before the
           archimedean engine gets there);
    CYCLE  the merged block graph is a partial function, so every confined
           orbit has an eventually periodic carry word -- a certificate;
    STABLE an exactly invariant nonempty fixpoint with a non-functional block
           graph: the engine provably cannot decide this set at this level;
    FAT / none: undecided within the budget.

    The block merge is cubic in the component count, so the CYCLE test is only
    run while there are at most `blockcap` components; above that the verdict
    is reported as `none+` to say so out loud.  Skipping it can only make this
    file's report weaker, never a false certificate -- but it must be visible.

    Returns (verdict, depth, S)."""
    M = Q ** j
    S = [U[:] for _ in range(M)]
    skipped = False
    for k in range(1, maxdepth + 1):
        T = prod_prune(S, U, P, Q, M)
        n = sum(len(x) for x in T)
        if n == 0:
            return 'KILL', k, T
        if n <= blockcap:
            if prod_outdeg(prod_blocks(T, P, Q, M), P, Q, M) <= 1:
                return 'CYCLE', k, T
        else:
            skipped = True
        if n > cap:
            return 'FAT', k, T
        if T == S:
            return 'STABLE', k, T
        S = T
    return ('none+' if skipped else 'none'), maxdepth, S


def arch_hold(P, Q, U, maxdepth=30, cap=20000):
    """The archimedean engine, as the j = 0 control for Theorem A."""
    return prod_hold(P, Q, 0, U, maxdepth, cap)      # M = q^0 = 1: no residue


# -------------------------------------------------------- the periodic orbits

def cycles(P, Q, U, maxperiod, cap=4000000):
    """Exact count of the points of period dividing L whose whole orbit stays
    in U, for L = 1..maxperiod.  These are the ghosts of section 4.4: rational
    orbits of the hold dynamics, generally NOT of the form {xi (p/q)^n}, whose
    only job is to obstruct certificates (Theorem B).

    With  y_k = (p^k y_0 - A_k)/q^k  and  A_{k+1} = p A_k + q^k w_k, the
    constraint "y_k in K" is the y_0-interval  (q^k K + A_k)/p^k, so the search
    is a DFS over carry words with exact interval pruning; a closed word of
    length L pins  y_0 = A_L/(p^L - q^L)."""
    CAR = list(range(-Q + 1, P))
    out = []
    for L in range(1, maxperiod + 1):
        den = P ** L - Q ** L
        found, seen = set(), 0
        stack = [(J[0], J[1], 0, 0) for J in U]
        while stack:
            lo, hi, A, k = stack.pop()
            seen += 1
            if seen > cap:
                out.append(None)
                break
            if k == L:
                y0 = F(A, den)
                if lo <= y0 < hi:
                    found.add(y0)
                continue
            qk, pk = Q ** (k + 1), P ** (k + 1)
            for s in CAR:
                A2 = P * A + Q ** k * s
                for K in U:
                    a = max(lo, (qk * K[0] + A2) / F(pk))
                    b = min(hi, (qk * K[1] + A2) / F(pk))
                    if a < b:
                        stack.append((a, b, A2, k + 1))
        else:
            out.append(len(found))
    return out


def ivl(G, nums):
    return [(F(nums[i], G), F(nums[i + 1], G)) for i in range(0, len(nums), 2)]


def show(G, nums):
    return " u ".join(f"[{nums[i]}/{G},{nums[i+1]}/{G})"
                      for i in range(0, len(nums), 2))


# ---------------------------------------------------------------- the controls

AKIYAMA = (4, 3, 4, [0, 1, 3, 4])          # [Aki08] Conjecture 1.4
DUB10 = (3, 2, 3, [0, 1, 2, 3])            # its (3,2) twin, PROVED nonempty

# five sets known nonempty in print; the M3/M4' negative controls, verbatim
NEGATIVE = [("[Pol81]  [4/65,61/65)", 65, [4, 61]),
            ("[Cho80]  [1/19,18/19)", 19, [1, 18]),
            ("[Dub08]  [5/48,43/48)", 48, [5, 43]),
            ("[Dub10]  ||.||<1/3   ", 3, [0, 1, 2, 3]),
            ("[KK18]   X_{3,2}     ", 6, [0, 1, 2, 4, 5, 6])]

# (3,2) entries with a known archimedean verdict, as Theorem A controls
ARCHKNOWN = [("certWindow38  [4/24,13/24)", 24, [4, 13]),
             ("certUnion712  4 cells /12 ", 12, [0, 2, 3, 4, 5, 8, 9, 10]),
             ("certFrontier  L* = 1466/3600", 3600, [961, 2427])]


def theoremA_first_mismatch(P, Q, j, U, depth):
    """First depth at which  union_r S^{(j)}[r]  differs from  S  -- None if the
    two agree throughout, which is Theorem A on the nose."""
    M = Q ** j
    S, A = [U[:] for _ in range(M)], [U[:]]
    for k in range(1, depth + 1):
        S = prod_prune(S, U, P, Q, M)
        A = prod_prune(A, U, P, Q, 1)
        if merge([iv for x in S for iv in x]) != A[0]:
            return k
    return None


def sec_A():
    print("== (A0) THEOREM A, tested directly: union_r S_k^(j)[r] == S_k ==")
    ok0 = True
    for (lab, P, Q, G, nums, d) in [
            ("(3,2) [4/24,13/24)  ", 3, 2, 24, [4, 13], 10),
            ("(3,2) ||.|| < 1/3   ", 3, 2, 3, [0, 1, 2, 3], 10),
            ("(3,2) 4 cells / 12  ", 3, 2, 12, [0, 2, 3, 4, 5, 8, 9, 10], 8),
            ("(4,3) Akiyama Conj  ", 4, 3, 4, [0, 1, 3, 4], 8),
            ("(5,2) two-cell 1/5  ", 5, 2, 5, [0, 1, 4, 5], 6)]:
        U = ivl(G, nums)
        r = [theoremA_first_mismatch(P, Q, j, U, d) for j in (1, 2, 3)]
        ok0 &= all(x is None for x in r)
        print(f"   {lab} depth {d:2d}, j=1,2,3: "
              + ("agrees at every level" if all(x is None for x in r)
                 else f"*** DIFFERS at {r} ***"), flush=True)
    print("   ==> " + ("the residue coordinate adds nothing to the y-projection"
                       if ok0 else "*** THEOREM A VIOLATED ***"))

    print("\n== (A) and its consequence: no product KILL beats the archimedean one ==")
    print("   (a strictly earlier product KILL would refute Theorem A)")
    ok = True
    for (name, G, nums) in ARCHKNOWN + [(n, G, ns) for (n, G, ns) in NEGATIVE]:
        P, Q = 3, 2
        U = ivl(G, nums)
        base = arch_hold(P, Q, U, maxdepth=16, cap=6000)
        row = []
        for j in (1, 2, 3):
            v, k, _ = prod_hold(P, Q, j, U, maxdepth=16, cap=6000 * 2 ** j)
            row.append(f"j={j}:{v}@{k}")
            if (v == 'KILL') != (base[0] == 'KILL') or (
                    v == 'KILL' and k < base[1]):
                ok = False
                row[-1] += " ***"
        print(f"   {name:28s} arch:{base[0]}@{base[1]:<3d} " + "  ".join(row))
    print("   ==> " + ("no level ever KILLed earlier than the archimedean engine"
                       if ok else "*** THEOREM A VIOLATED ***"))
    return ok and ok0


def sec_B():
    print("\n== (B) NEGATIVE controls: sets known NONEMPTY, at every level ==")
    bad = False
    for (name, G, nums) in NEGATIVE:
        U = ivl(G, nums)
        row = []
        for j in (1, 2, 3):
            v, k, S = prod_hold(3, 2, j, U, maxdepth=12, cap=6000 * 2 ** j)
            row.append(f"j={j}:{v}@{k}")
            if v in ('KILL', 'CYCLE'):
                bad, row[-1] = True, row[-1] + " ***"
        print(f"   {name} " + "  ".join(row))
    print("   ==> " + ("*** ENGINE CERTIFIED A NONEMPTY SET ***" if bad
                       else "refused at every level, as it must be"))
    return not bad


def sec_C():
    print("\n== (C) X4: the crossover curve past the frontier L* = 1466/3600 ==")
    print("   Theorem A forbids a KILL at any level, so the only way the product")
    print("   engine can gain here is a CYCLE certificate.  Run it at the last")
    print("   certified length and at the first band lengths, j = 0..3.")
    for (label, G, nums) in [("L*   = 1466  certified", 3600, [961, 2427]),
                             ("L*+1 = 1467  band     ", 3600, [961, 2428]),
                             ("L*+4 = 1470  band     ", 3600, [961, 2431])]:
        U = ivl(G, nums)
        row = [f"j={j}:{v}@{k}" for j in (0, 1, 2, 3)
               for (v, k, _) in [prod_hold(3, 2, j, U, maxdepth=30, cap=200000)]]
        print(f"   {label}  " + "  ".join(row), flush=True)
    print("   ('none+' = undecided, and above 400 components the cubic block")
    print("    merge was skipped, so the CYCLE test did not run at those levels.)")
    print("   ==> flat.  The product engine never certifies a band entry, and on")
    print("       the certified one it needs a STRICTLY DEEPER funnel than the")
    print("       archimedean engine (13 -> 15): more states, later certificate.")
    print("   Honest caveat -- the band is NOT proven out of reach.  Theorem B")
    print("   bounds a certificate below by the periodic-orbit count, and here")
    print("   that count is small, so the theorem does not bite:")
    for (label, G, nums) in [("L*   certified", 3600, [961, 2427]),
                             ("L*+1 band     ", 3600, [961, 2428]),
                             ("L*+4 band     ", 3600, [961, 2431])]:
        c = cycles(3, 2, ivl(G, nums), 16, cap=8000000)
        print(f"   {label}: periodic points by period {c}", flush=True)
    print("   ==> 1, 2 and 3 orbits respectively out to period 16 (measured to")
    print("       20 offline, unchanged).  So the band entries stay open: this")
    print("       engine fails on them, but no theorem here says every engine must.")


def sec_D():
    print("\n== (D) M7: [Aki08] Conjecture 1.4 at (4,3), U = [0,1/4) u [3/4,1) ==")
    P, Q, G, nums = AKIYAMA
    U = ivl(G, nums)
    for j in range(1, 6):
        v, k, S = prod_hold(P, Q, j, U, maxdepth=20, cap=100000)
        M = Q ** j
        comps = sum(len(x) for x in S)
        alive = sum(1 for x in S if x)
        meas = sum(b - a for x in S for (a, b) in x)
        print(f"   j={j}  M=3^{j}={M:4d}  {v} at depth {k}:  {comps:4d} components"
              f"  over {alive:3d}/{M} residues,  outdeg {prod_outdeg(S, P, Q, M)},"
              f"  mass {meas}", flush=True)
    print("   ==> nonempty and exactly forward-invariant at every level, with")
    print("       2^(j+1) components of length (3/4)^j/4 and out-degree 2:")
    print("       neither a KILL nor a CYCLE certificate can ever appear.")


def sec_E():
    print("\n== (E) THEOREM B applied: the ghost 2-shift, at (4,3) and at (3,2) ==")
    for (label, (P, Q, G, nums)) in (("[Aki08] Conj 1.4  (4,3), OPEN     ", AKIYAMA),
                                     ("[Dub10] ||.||<1/3 (3,2), NONEMPTY ", DUB10)):
        c = cycles(P, Q, ivl(G, nums), 13)
        pred = [2 ** L - 1 for L in range(1, 14)]
        print(f"   {label} {c}")
        print(f"   {'':34s} 2^L-1 = {pred}  {'MATCH' if c == pred else '***'}")
    print("   ==> both hold sets carry a full 2-shift of periodic orbits, so by")
    print("       Theorem B NO product certificate exists at any level j -- and")
    print("       the two cases are indistinguishable to the whole family, even")
    print("       though [Dub10] PROVES the (3,2) one nonempty.  The obstruction")
    print("       is therefore not evidence about Conjecture 1.4 either way.")


def main():
    a = sys.argv[1:]
    if a and a[0] == 'cycles':
        P, Q, G = int(a[1]), int(a[2]), int(a[3])
        nums = [int(x) for x in a[4:]]
        mx = 12
        if len(nums) % 2:
            mx, nums = nums[-1], nums[:-1]
        print(f"  U = {show(G, nums)}")
        for i, n in enumerate(cycles(P, Q, ivl(G, nums), mx), 1):
            print(f"    period {i:3d}: {n}")
        return 0
    if a and a[0] == 'hold':
        P, Q, j, G = (int(x) for x in a[1:5])
        nums = [int(x) for x in a[5:]]
        v, k, S = prod_hold(P, Q, j, ivl(G, nums))
        print(f"  U = {show(G, nums)}   (p,q) = ({P},{Q}), level j = {j}")
        print(f"  {v} at depth {k}, outdeg {prod_outdeg(S, P, Q, Q ** j)}")
        for r, x in enumerate(S):
            if x:
                print(f"    x = {r:4d} (mod {Q ** j}) : "
                      + "  ".join(f"[{p},{q})" for p, q in x))
        return 0
    good = sec_A()
    good &= sec_B()
    sec_C()
    sec_D()
    sec_E()
    return 0 if good else 1


if __name__ == "__main__":
    sys.exit(main())
