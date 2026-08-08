#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
"""horseshoe.py -- plan-M5A9 milestone N2(a): the positive side of the phi_model
ledger.  Searches for, and re-checks, the horseshoe certificates of
`Z32/ModelEntropy.lean`.

The model (same conventions as atlas.c and BlockCert.lean, plan-cert32 sec. 1.1):

    q*y_{n+1} = p*y_n - s_n,     forward branch   f_s(y) = (p y - s)/q
                                 inverse branch   h_s(x) = (q x + s)/p .

For a word w = (s_0..s_{L-1}) put H_w = h_{s_0} o ... o h_{s_{L-1}}, the inverse
of f_w and a contraction of ratio (q/p)^L.  A *horseshoe certificate* for U is a
closed interval K = [A/D, B/D] together with N >= 2 distinct words of a common
length L such that, for every one of them,

    H_{(s_i..s_{L-1})}(K) subset U    for every i < L      ("visits U")
    H_w(K) subset K                                        ("invariance").

Then every concatenation of those words fixes a point of K (intermediate value
theorem) whose whole orbit stays in U, so the hold set's carry language has at
least N^k words of length kL and

    phi_model(U) >= log N / L .

Since any invariant K must contain the fixed point of each H_w, the *minimal*
candidate is the hull of those fixed points: if the hull fails, every K fails.
That is what makes the search below exhaustive at each length.

Usage
  python3 horseshoe.py --check                 re-check the four shipped entries
  python3 horseshoe.py --search band 10        search [0,5/12) up to length 10
  python3 horseshoe.py --search twocell 7      search [0,1/3) u [2/3,1)
  python3 horseshoe.py --points band 6         no point carries two return words
"""
import sys
from fractions import Fraction as F
from itertools import product
from math import log, lcm

# ---------------------------------------------------------------------------
# the exact integer replay of `Z32.Horse.ok` -- this is what the kernel checks
# ---------------------------------------------------------------------------


def check_word(D, p, q, U, A, B, w, closed=False):
    """Replay `suffixOk` and the two final containments for one word.

    Numerators are carried over the denominator D*p^j after j backward steps, so
    every test is an integer comparison, exactly as in Lean."""
    X, Y, k = A, B, 1
    for s in reversed(w):
        X, Y, k = q * X + s * D * k, q * Y + s * D * k, p * k
        inside = any(a * k <= X and (Y <= b * k if closed else Y < b * k) for a, b in U)
        if not inside:
            return False
    return A * k <= X and Y <= B * k


def check_cert(D, p, q, U, A, B, words, closed=False):
    if not (0 < D and 0 < q < p and A <= B):
        return False
    if not all(0 <= a and (b < D if closed else b <= D) for a, b in U):
        return False
    if len(words) < 2 or len({tuple(w) for w in words}) != len(words):
        return False
    if len({len(w) for w in words}) != 1 or len(words[0]) == 0:
        return False
    return all(check_word(D, p, q, U, A, B, w, closed) for w in words)


# ---------------------------------------------------------------------------
# independent validation: every concatenation is a genuine admissible orbit
# ---------------------------------------------------------------------------


def fixed(w, p, q):
    """The unique point with periodic carry word w: y = sum p^{L-1-i} q^i s_i / (p^L - q^L)."""
    L = len(w)
    return F(sum(p ** (L - 1 - i) * q**i * w[i] for i in range(L)), p**L - q**L)


def orbit_ok(w, U, p, q):
    """Is the whole periodic orbit of the fixed point of w inside U and [0,1)?"""
    y = x = fixed(w, p, q)
    for s in w:
        if not any(a <= x < b for a, b in U):
            return False
        if not (0 <= x < 1):
            return False
        x = (p * x - s) / q
    return x == y


def validate(D, p, q, U, A, B, words, kmax=2):
    """Brute force: check every concatenation of up to kmax blocks, from scratch."""
    Uf = [(F(a, D), F(b, D)) for a, b in U]
    bad = 0
    for k in range(1, kmax + 1):
        for choice in product(range(len(words)), repeat=k):
            W = [s for j in choice for s in words[j]]
            if not orbit_ok(W, Uf, p, q):
                bad += 1
    return bad


# ---------------------------------------------------------------------------
# the search
# ---------------------------------------------------------------------------


def images_ok(w, K, U, p, q):
    lo, hi = K
    for s in reversed(w):
        lo, hi = (q * lo + s) / p, (q * hi + s) / p
        if not any(a <= lo and hi < b for a, b in U):
            return False
    return K[0] <= lo and hi <= K[1]


def best_at(U, L, p=3, q=2):
    """The best word set at length L: maximise N over hulls of admissible fixed points."""
    good = [w for w in product(range(1 - q, p), repeat=L) if orbit_ok(list(w), U, p, q)]
    pts = sorted({fixed(w, p, q) for w in good})
    best = None
    for i, lo in enumerate(pts):
        for hi in pts[i:]:
            S = [w for w in good if images_ok(w, (lo, hi), U, p, q)]
            if len(S) >= 2 and (best is None or len(S) > len(best[1])):
                best = ((lo, hi), S)
    return len(good), best


SETS = {
    "band": [(F(0), F(5, 12))],
    "twocell": [(F(0), F(1, 3)), (F(2, 3), F(1))],
    "window38": [(F(1, 6), F(13, 24))],
    "frontier": [(F(961, 3600), F(2427, 3600))],
}

# the four entries of Z32/ModelEntropy.lean, in the file's own integer form
ENTRIES = [
    ("horseBand", 108, [(0, 45)], 0, 12,
     [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0]]),
    ("horseBandRecord", 180, [(0, 75)], 0, 22,
     [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 0, 1, 0],
      [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
      [0, 0, 0, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 1, 0, 0]]),
    ("horseTwoCellSmall", 57, [(0, 19), (38, 57)], 0, 15,
     [[-1, 1, 2], [-1, 2, 0], [0, -1, 2], [0, 0, 0]]),
    ("horseTwoCell", 633, [(0, 211), (422, 633)], 0, 195,
     [[-1, 1, 1, 1, 2], [-1, 1, 1, 2, 0], [-1, 1, 2, -1, 2], [-1, 1, 2, 0, 0],
      [-1, 2, -1, 1, 2], [-1, 2, -1, 2, 0], [-1, 2, 0, -1, 2], [-1, 2, 0, 0, 0],
      [0, -1, 1, 1, 2], [0, -1, 1, 2, 0], [0, -1, 2, -1, 2], [0, -1, 2, 0, 0],
      [0, 0, -1, 1, 2], [0, 0, -1, 2, 0], [0, 0, 0, -1, 2], [0, 0, 0, 0, 0]]),
]


def cmd_check():
    """Re-check every shipped entry, and validate it independently."""
    ok = True
    for name, D, U, A, B, words in ENTRIES:
        N, L = len(words), len(words[0])
        c = check_cert(D, 3, 2, U, A, B, words)
        bad = validate(D, 3, 2, U, A, B, words, kmax=(3 if N <= 4 else 2))
        rate = log(N) / L
        print(f"{name:20s} D={D:5d} N={N:2d} L={L:2d}  ok={c}  "
              f"inadmissible concatenations={bad}  phi >= log {N}/{L} = {rate:.4f}")
        ok = ok and c and bad == 0
    print("ALL ENTRIES RE-CHECKED" if ok else "FAILURE")
    return 0 if ok else 1


def cmd_points(name, lmax, p=3, q=2):
    """Why the certificate has to be about intervals, not points.

    A "two loops at one point" certificate would be a point of the hold set with
    two distinct return words of the same length.  There is none: the branching
    of the carry relation separates points immediately, so distinct words have
    distinct periodic points and the interval form above is necessary."""
    U = SETS[name]
    for L in range(1, lmax + 1):
        seen = {}
        for w in product(range(1 - q, p), repeat=L):
            if orbit_ok(list(w), U, p, q):
                seen.setdefault(fixed(w, p, q), []).append(w)
        multi = {y: ws for y, ws in seen.items() if len(ws) > 1}
        print(f"  L={L:2d}: {len(seen):4d} admissible periodic points, "
              f"{len(multi)} carrying two or more words")
    return 0


def cmd_search(name, lmax):
    U = SETS[name]
    print(f"U = {[f'[{a},{b})' for a, b in U]}   total {sum(b - a for a, b in U)}")
    for L in range(1, lmax + 1):
        n, best = best_at(U, L)
        if best is None:
            print(f"  L={L:2d}: {n:4d} admissible periodic words, no horseshoe")
            continue
        K, S = best
        den = lcm(3, K[0].denominator, K[1].denominator)
        print(f"  L={L:2d}: {n:4d} admissible words | N={len(S):3d} K=[{K[0]},{K[1]}] "
              f"(D={den}) rate=log({len(S)})/{L}={log(len(S))/L:.4f}")
    return 0


if __name__ == "__main__":
    if len(sys.argv) >= 2 and sys.argv[1] == "--check":
        sys.exit(cmd_check())
    if len(sys.argv) >= 3 and sys.argv[1] == "--search":
        sys.exit(cmd_search(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 6))
    if len(sys.argv) >= 3 and sys.argv[1] == "--points":
        sys.exit(cmd_points(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 6))
    print(__doc__)
