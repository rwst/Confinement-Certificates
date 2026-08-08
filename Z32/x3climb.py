#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# x3climb.py -- plan-cert32 milestone M2, experiment X3: hill-climb the
# certified-empty union record.  A union that is certified at one cell
# resolution is the same SET at any finer resolution, so the record can only
# improve under refinement; this driver refines the current best union to a
# finer grid and greedily adds cells while the certificate survives.
#
# It drives the C engine as a black box (subprocess), so it is also an
# end-to-end check of the command-line interface the atlas tables quote.
#
#   ./x3climb.py <N0> <cell> <cell> ...      # seed = these cells of 1/N0
#   ./x3climb.py 120 0 1 2 ...

import random
import subprocess
import sys

ATLAS = "./atlas"
DEPTH = 30


def intervals(cells, N):
    out, cs = [], sorted(cells)
    for c in cs:
        if out and out[-1][1] == c:
            out[-1] = (out[-1][0], c + 1)
        else:
            out.append((c, c + 1))
    return out


def certified(cells, N):
    if not cells:
        return True
    args = [ATLAS, "cert", str(DEPTH), str(N)]
    for lo, hi in intervals(cells, N):
        args += [str(lo), str(hi)]
    out = subprocess.run(args, capture_output=True, text=True).stdout
    return " KILL " in out or " CYCLE " in out


def main():
    N = int(sys.argv[1])
    seed = set(int(x) for x in sys.argv[2:])
    assert certified(seed, N), "seed union is not certified"
    rng = random.Random(20260726)
    cur = set(seed)
    improved = True
    while improved:
        improved = False
        order = [c for c in range(N) if c not in cur]
        rng.shuffle(order)
        for c in order:
            trial = cur | {c}
            if certified(trial, N):
                cur = trial
                improved = True
                print(f"# +cell {c}: |U| = {len(cur)}/{N} = {len(cur)/N:.9f}", flush=True)
    print(f"BEST {len(cur)}/{N} = {len(cur)/N:.9f}")
    print("U =", " ".join(f"[{a}/{N},{b}/{N})" for a, b in intervals(cur, N)))
    print("cells:", " ".join(str(c) for c in sorted(cur)))


if __name__ == "__main__":
    main()
