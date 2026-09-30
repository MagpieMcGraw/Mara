#!/usr/bin/env bash
# The new checker's differential (design/flat_tree.md, stage 3). Every program
# irdiff.sh builds is built twice, by the old checker and by the new one
# (MARA_CHECKER=new, tcnew.sh). Their build output, IR and — with -r — runs
# are compared. A program matches when all of them do, and the count is the
# new checker's progress. Programs that matched before (tc_match.txt) and
# don't now are regressions, and fail the run.
#
#   test/tcdiff.sh        IR byte-identical
#   test/tcdiff.sh -n     IR modulo naming (irnorm.pl)
#   test/tcdiff.sh -r     also run both builds and compare
#   test/tcdiff.sh -u     record this run's matches as tc_match.txt
#
# Both sides are kept under $OUT/old and $OUT/new, and each program's verdict
# is in $OUT/verdicts.txt.
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=${OUT:-${TMP:-/tmp}/mara_tcdiff}
NORMALIZE=0 RUN=0 UPDATE=0
pass=()
for a in "$@"; do
  case $a in
    -n) NORMALIZE=1; pass+=("$a") ;;
    -r) RUN=1; pass+=("$a") ;;
    -u) UPDATE=1 ;;
    *)  pass+=("$a") ;;
  esac
done
SIDES="old:$ROOT/Mara.exe new:$ROOT/test/tcnew.sh" OUT=$OUT \
  bash "$ROOT/test/irdiff.sh" "${pass[@]}" > /dev/null 2>&1

verdicts=$OUT/verdicts.txt
: > "$verdicts"
matched=0 total=0
for o in "$OUT"/old/*.out; do
  mod=$(basename "$o" .out)
  total=$((total + 1))
  why=""
  cmp -s "$o" "$OUT/new/$mod.out" || why="output"
  if [ -z "$why" ]; then
    x=(); if [ $NORMALIZE = 1 ]; then x=(-x '*.ll'); else x=(-x '*.norm'); fi
    if [ -d "$OUT/old/$mod" ] || [ -d "$OUT/new/$mod" ]; then
      diff -r "${x[@]}" "$OUT/old/$mod" "$OUT/new/$mod" > /dev/null 2>&1 || why="ir"
    fi
  fi
  if [ -z "$why" ] && [ $RUN = 1 ] && [ -f "$OUT/run/old/$mod.run" ]; then
    cmp -s "$OUT/run/old/$mod.run" "$OUT/run/new/$mod.run" || why="run"
  fi
  if [ -z "$why" ]; then
    matched=$((matched + 1)); echo "$mod match" >> "$verdicts"
  else
    echo "$mod $why" >> "$verdicts"
  fi
done
sort -o "$verdicts" "$verdicts"
grep ' match$' "$verdicts" | cut -d' ' -f1 > "$OUT/matched.txt"
explained_file=$ROOT/test/tc_explained.txt
explained=0
if [ -f "$explained_file" ]; then
  for mod in $(grep -v "^#" "$explained_file" | awk 'NF {print $1}'); do
    if grep -q "^$mod " "$verdicts" && ! grep -q "^$mod match$" "$verdicts"; then explained=$((explained + 1)); fi
  done
fi
echo "TCDIFF: $matched of $total programs match, $explained more differ as explained (test/tc_explained.txt)"

status=0
record=$ROOT/test/tc_match.txt
if [ -f "$record" ]; then
  lost=$(comm -23 <(sort "$record") "$OUT/matched.txt")
  gained=$(comm -13 <(sort "$record") "$OUT/matched.txt" | wc -l)
  [ "$gained" -gt 0 ] && echo "  $gained newly matching"
  if [ -n "$lost" ]; then
    echo "  REGRESSED (matched before):"; echo "$lost" | sed 's/^/    /'; status=1
  fi
fi
[ $UPDATE = 1 ] && cp "$OUT/matched.txt" "$record" && echo "  recorded in test/tc_match.txt"
exit $status
