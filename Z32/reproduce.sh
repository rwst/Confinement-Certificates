#!/bin/sh
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# reproduce.sh -- plan-cert32 milestone M2: regenerate every number in
# Z32/README.md from scratch.  Deterministic: no timing, no randomness except
# the printed seed of the X3 greedy search.  Total runtime ~1 minute except
# where marked.
#
#   cd Z32 && sh reproduce.sh          # writes data/*.txt, prints checksums

set -e
cc=${CC:-gcc}
$cc -O2 -o hold     hold.c     -lm
$cc -O2 -o atlas    atlas.c    -lm
$cc -O2 -o gridcert gridcert.c -lm
mkdir -p data

echo "== X1 control: FLP95 Cor 1.4a escape orbits (expect N = 3,2,3,1) =="
for a in 1 2 3 4; do ./hold orbit $a 2 6 20; done  > data/x1_flp_orbits.txt
grep esc0 data/x1_flp_orbits.txt

echo "== X1 sweep: L = 1/3, s = i/G, theta-model =="
: > data/x1_sweep.txt
for G in 6 12 24 48 96 192 384 768 1536 3072 3888; do
  ./hold x1 $G 36 | tail -1 >> data/x1_sweep.txt
done
cat data/x1_sweep.txt

echo "== X1 cross-check: same five positions in the y-model =="
for a in 0 1 2 3 4; do ./atlas win 40 6 $a 2 | grep verdict; done | tee data/x1_ymodel.txt

echo "== X2: the (position,length) map, G = 360, lengths 1/3 .. 1/2 =="
ATLAS_CAP=20000 ./atlas x2 360 120 180 30 > data/x2_G360.txt 2>&1
grep '^# row' data/x2_G360.txt | head -30

echo "== X2 frontier: G = 3600 near L* (30 s) =="
ATLAS_CAP=20000 ATLAS_ILO=940 ATLAS_IHI=1240 ./atlas x2 3600 1455 1470 30 > data/x2_frontier.txt 2>&1
ATLAS_CAP=20000 ./atlas x2 3600 1467 1475 30 >> data/x2_frontier.txt 2>&1
grep '^# row' data/x2_frontier.txt

echo "== X2 no-go witnesses: cycle counts inside band entries =="
{ for w in "24 0 10" "360 0 150" "6 2 4" "24 4 13"; do
    set -- $w
    printf "U=[%s/%s,%s/%s) : " $2 $1 $3 $1
    ./atlas horse 12 $1 $2 $3 | grep 'cycles found'
  done; } | tee data/x2_cycles.txt

echo "== X3 literature controls =="
{ printf "[Dub08] Cor 1.2, U = [8/39,18/39) u [21/39,31/39), |U| = 20/39: "
  ./atlas cert 30 39 8 18 21 31 | grep verdict
  printf "[Dub06] complement, |U| = 0.476234: "
  ./atlas cert 30 1000000 0 238117 761883 1000000 | grep verdict
} | tee data/x3_controls.txt

echo "== X3 NEGATIVE controls: sets known NONEMPTY must come back undecided =="
{ printf "[KK18] Cor 4.8  X_{3,2}, |U|=2/3     : "; ./atlas cert 30 6 0 1 2 4 5 6 | grep -o "verdict [A-Z]*"
  printf "[Dub10] (1.1)   ||.||<1/3, |U|=2/3   : "; ./atlas cert 30 3 0 1 2 3 | grep -o "verdict [A-Z]*"
  printf "[Pol81]         [4/65,61/65)         : "; ./atlas cert 30 65 4 61 | grep -o "verdict [A-Z]*"
  printf "[Dub08] Thm 1.3 (5/48,43/48)         : "; ./atlas cert 30 48 5 43 | grep -o "verdict [A-Z]*"
  printf "[Cho80]         [1/19,18/19)         : "; ./atlas cert 30 19 1 18 | grep -o "verdict [A-Z]*"
} | tee data/x3_negative.txt

echo "== X3 exhaustive union search (records; N0 = 20 takes ~2 min) =="
for N in 12 16 18 20; do ./atlas x3exh $N 30 | tail -2; done | tee data/x3_exhaustive.txt

echo "== X3 randomized search + refinement climb =="
for N in 36 48 60; do ./atlas x3 $N 4000 28 | tail -2; done | tee data/x3_random.txt
echo "(the 120- and 240-cell records come from x3climb.py seeded by the 60-cell"
echo " winner; see README.  python3 x3climb.py 120 <cells>)"

echo "== record union, verified three ways =="
R240="0 8 12 32 36 48 52 88 100 104 108 128 132 152 161 184 190 191 192 208 216 224 228 237 238 239"
{ printf "C engine   : "; ./atlas cert 30 240 $R240 | grep verdict
  printf "falsify    : "; ./atlas horse 10 240 $R240 | tail -1
  printf "python lvls: "; python3 verify_atlas.py 18 240 $R240 --all --nocert |
      awk '$1=="level"&&$2+0>=15{printf "%s:%s ",$2,$4}'; echo
  printf "C lvls     : "; ATLAS_FULL=1 ./atlas cert 18 240 $R240 |
      awk 'NF==2&&$1+0>=15{printf "%s:%s ",$1,$2}'; echo
} | tee data/x3_record.txt

echo "== checksums =="
md5sum data/*.txt

# ---------------------------------------------------------------------------
# Milestone M3: the Lean bridge.  `gencert.py` re-runs the exact pruning and
# emits the funnel that `Z32/BlockCert.lean` hands to the kernel; these runs
# regenerate every certificate in that file byte for byte, and confirm that the
# generator refuses the five sets known NONEMPTY in print.
# ---------------------------------------------------------------------------

echo "== M3/M6 certificates (must match the defs in Z32/BlockCert.lean) =="
{ python3 gencert.py --closed --ranked 39 8 18 21 31          --lean certDub08
  python3 gencert.py 24 4 13                                  --lean certWindow38
  python3 gencert.py 12 0 2 3 4 5 8 9 10                      --lean certUnion712
  python3 gencert.py 18 0 2 3 8 9 10 11 14 15 16              --lean certUnion23
  python3 gencert.py 3600 961 2427                            --lean certFrontier
  python3 gencert.py 36 0 3 4 11 16 24 25 27 30 32 33 36      --lean certUnion2536
  python3 gencert.py 5 0 1 4 5                                --lean certTwoCellFifth
  python3 gencert.py --pq 4 3 24 8 15                         --lean certFourThree
  python3 gencert.py --pq 5 2 5 1 2                           --lean certFiveTwo
  # the p > q^2 table: six positions s = i/6 at each of five bases, all depth 1
  for i in 0 1 2 3 4 5; do
    python3 gencert.py --pq 5  2 30 $((i*5))  $((i*5+6))  --lean certGridFiveTwo$i
  done
  for i in 0 1 2 3 4 5; do
    python3 gencert.py --pq 7  2 42 $((i*7))  $((i*7+6))  --lean certGridSevenTwo$i
  done
  for i in 0 1 2 3 4 5; do
    python3 gencert.py --pq 9  2 18 $((i*3))  $((i*3+2))  --lean certGridNineTwo$i
  done
  for i in 0 1 2 3 4 5; do
    python3 gencert.py --pq 10 3 30 $((i*5))  $((i*5+3))  --lean certGridTenThree$i
  done
  for i in 0 1 2 3 4 5; do
    python3 gencert.py --pq 11 3 66 $((i*11)) $((i*11+6)) --lean certGridElevenThree$i
  done
} > data/m3_certs.txt
grep -E '^(def|# \(V2)' data/m3_certs.txt
diff <(grep -E '^\s+(D :=|p :=|q :=|closed :=|U :=|\[\()' data/m3_certs.txt) \
     <(grep -E '^\s+(D :=|p :=|q :=|closed :=|U :=|\[\()' BlockCert.lean) \
  && echo "certificates in BlockCert.lean are byte-identical to this run"

echo "== the union record (17/24), checked against Z32/UnionRecord.lean =="
echo "  (SLOW: the kernel check of this one costs ~100 s and ~12 GB; the"
echo "   generator run below is the cheap half)"
python3 gencert.py 48 0 2 3 9 10 11 12 16 17 18 20 21 23 34 36 37 38 40 41 45 46 47 \
  --lean certUnion7083 > data/m3_union_record.txt
diff <(grep -E '^\s+(D :=|U :=|\[\()' data/m3_union_record.txt) \
     <(grep -E '^\s+(D :=|U :=|\[\()' UnionRecord.lean) \
  && echo "certUnion7083 in UnionRecord.lean is byte-identical to this run"

echo "== the two-cell frontier: c = 1/5 certifies, c = 21/100 and closed do not =="
python3 gencert.py 100 0 21 79 100 | tail -1
python3 gencert.py --closed 5 0 1 4 5 | tail -1

echo "== M3 negative controls: no certificate for sets known NONEMPTY =="
{ for w in "65 4 61" "19 1 18" "48 5 43" "3 0 1 2 3" "6 0 1 2 4 5 6"; do
    printf "%-22s : " "[$w]"
    python3 gencert.py $w 2>&1 | grep -E "no certificate|V2\) and|KILL" | head -1
  done; } | tee data/m3_negative.txt

echo "== M4' P1 negative controls: same five refused in the STRONGEST mode too =="
{ for w in "65 4 61" "19 1 18" "48 5 43" "3 0 1 2 3" "6 0 1 2 4 5 6"; do
    printf "%-22s : " "[$w]"
    python3 gencert.py --closed --ranked $w 2>&1 |
      grep -E "no certificate|V2\) and|KILL" | head -1
  done; } | tee data/m4_negative_closed.txt

echo "== M6 base-independence: the (3,2) path must be BYTE-IDENTICAL to M3 =="
{ python3 gencert.py --pq 3 2 24 4 13 --lean certWindow38
} > data/m6_default.txt
diff <(grep -E '^\s+(D :=|U :=|\[\()' data/m6_default.txt) \
     <(sed -n '/^def certWindow38/,/^$/p' data/m3_certs.txt |
       grep -E '^\s+(D :=|U :=|\[\()') \
  && echo "--pq 3 2 reproduces the default (3,2) certificate exactly"

echo "== M6 controls: a second base, in both colors (SLOW: ~1 h, mostly part C) =="
python3 pqcontrols.py | tee data/m6_controls.txt

# ---------------------------------------------------------------------------
# Milestone M7 / experiment X4: the section-4.3 product refinement, states
# (cell, x mod q^j).  The engine is built so that its two no-go theorems can be
# measured, not asserted: Theorem A (the product KILLs no earlier than the
# archimedean engine, ever) and Theorem B (a certificate needs one block per
# periodic orbit of the hold set).  Applied to [Aki08] Conjecture 1.4 they
# close it out: no certificate of this family exists at any level.
# ---------------------------------------------------------------------------

echo "== M7/X4 controls: the product refinement, in both colors (~90 s) =="
python3 prodcert.py | tee data/m7_controls.txt

echo "== M7 cross-check: the C engine must agree on the cycle counts =="
{ for w in "24 0 10" "3600 961 2427" "3600 961 2428"; do
    printf "atlas horse P<=12  U=[%-14s] : " "$w"
    ./atlas horse 12 $w | grep -i 'cycles found'
  done; } | tee data/m7_horse.txt
grep -q 'cycles found: 1 ' data/m7_horse.txt \
  && echo "(the two frontier entries have ONE cycle each -- band and certified alike)"

# ---------------------------------------------------------------------------
# plan-M5A9 milestone N2(a): the phi_model ledger.  `horseshoe.py` re-checks the
# four certificates of Z32/ModelEntropy.lean in the exact integer form the Lean
# kernel uses, and validates each one independently by expanding every
# concatenation of up to two (or three) blocks and testing its periodic orbit.
# The searches print the frontier of what this certificate shape can reach, and
# the two certified windows are the negative controls: a set with phi_model = 0
# can carry no horseshoe (Z32.not_cert_and_horse), and none is found.
# ---------------------------------------------------------------------------

echo "== N2(a) phi_model: re-check the four horseshoe certificates =="
python3 horseshoe.py --check | tee data/n2_horseshoes.txt
grep -q "ALL ENTRIES RE-CHECKED" data/n2_horseshoes.txt

echo "== N2(a) searches: the band entry, the two-cell hole, and two controls =="
{ echo "--- band [0,5/12)";        python3 horseshoe.py --search band 8
  echo "--- two-cell ||.||<1/3";   python3 horseshoe.py --search twocell 6
  echo "--- control [1/6,13/24)";  python3 horseshoe.py --search window38 6
  echo "--- control frontier";     python3 horseshoe.py --search frontier 6
} | tee data/n2_search.txt
grep -c "no horseshoe" data/n2_search.txt

echo "== N2(a) why intervals: no point carries two return words of one length =="
{ for s in band twocell window38; do echo "--- $s"; python3 horseshoe.py --points $s 6; done
} | tee data/n2_points.txt
grep -q "1 carrying" data/n2_points.txt && echo "UNEXPECTED: a point with two words" || \
  echo "(the two-cell counts are 2^L-1: a full shift on points, none of them shared)"

echo "== M3/M6/M7/N2 checksums =="
md5sum data/m3_*.txt data/m6_*.txt data/m7_*.txt data/n2_*.txt
