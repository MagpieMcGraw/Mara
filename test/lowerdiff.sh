#!/usr/bin/env bash
# Lowering differential (design/annotated_tree.md, stage 2). Builds every
# fixture with a main, the multifile fixtures, Pounce and design/all twice
# with the working compiler: the graph built while checking, and the graph
# lowered from the annotated tree once checking is done (MARA_LOWER=new) —
# each dumped whole (MARA_GRAPH=full). A program matches when the two dumps
# and the build outputs agree.
#
#   test/lowerdiff.sh          compare; report what matches, what doesn't
#   test/lowerdiff.sh -u       ... and record the matches in test/lower_match.txt
#   test/lowerdiff.sh -j N     N programs at a time (default: every core)
#
# A program in test/lower_match.txt that no longer matches fails the run.
# Lowering stopping (a form it doesn't lower yet) is listed with its reason.
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=${OUT:-${TMP:-/tmp}/mara_lowerdiff}
JOBS=$(nproc 2>/dev/null || echo 4)
UPDATE=0
while [ $# -gt 0 ]; do
  case $1 in
    -u) UPDATE=1 ;;
    -j) JOBS=$2; shift ;;
  esac
  shift
done
WORK=$ROOT/Mara.exe
rm -rf "$OUT"; mkdir -p "$OUT/old" "$OUT/new"
export ROOT OUT WORK

one_program() {  # dir module [build flags]
  local dir=$1 mod=$2 flags=$3 side
  for side in old new; do
    local lower=""
    [ $side = new ] && lower=new
    ( cd "$dir" && { rm -rf "${mod}_build" 2>/dev/null; MARA_LOWER=$lower MARA_GRAPH=full "$WORK" build "$mod" $flags 2>&1; } ) \
      | grep -E '^(graph:|n |e |r |s |u |settled |scope |\[|lower:)' | grep -v 'is ambiguous (defined in' \
      | awk '/^(\[|lower:)/ { d[n++] = $0; next } { print } END { for (i = 0; i < n; i++) print d[i] | "sort"; close("sort") }' > "$OUT/$side/$mod.dump"
  done
  rm -rf "$dir/${mod}_build" "$dir/$mod.exe" 2>/dev/null
}
export -f one_program

list=$OUT/programs.lst
: > "$list"
cd "$ROOT/test"
for f in *.mara; do
  grep -qE '^[[:space:]]*main[[:space:]]*::' "$f" && echo "$ROOT/test ${f%.mara}" >> "$list"
done
for d in "$ROOT"/test/*/; do
  d=${d%/}; [ -f "$d/.multifile" ] || continue
  if [ -f "$d/.shared" ]; then echo "$d $(basename "$d") -shared"; else echo "$d $(basename "$d")"; fi >> "$list"
done
echo "$ROOT/Pounce Pounce" >> "$list"
echo "$ROOT/design all" >> "$list"
xargs -P "$JOBS" -L 1 bash -c 'one_program "$0" "$1" "$2"' < "$list"

match=$OUT/match.txt
: > "$match"
stopped=0 differ=0
for f in "$OUT"/old/*.dump; do
  mod=$(basename "$f" .dump)
  if cmp -s "$f" "$OUT/new/$mod.dump"; then
    echo "$mod" >> "$match"
  elif grep -q 'Graph error: lower:' "$OUT/new/$mod.dump"; then
    stopped=$((stopped + 1))
  else
    differ=$((differ + 1))
  fi
done
total=$(ls "$OUT"/old/*.dump | wc -l)
echo "LOWERDIFF: $(wc -l < "$match") of $total programs match; $stopped stopped (lower: …), $differ differ"
echo "  what stopped lowering, most first:"
grep -h 'Graph error: lower:' "$OUT"/new/*.dump | sed -E 's/^.*Graph error: lower: //' | sort | uniq -c | sort -rn | head -20
lost=$(comm -23 <(sort "$ROOT/test/lower_match.txt" 2>/dev/null) <(sort "$match"))
if [ $UPDATE = 1 ]; then sort "$match" > "$ROOT/test/lower_match.txt"; fi
if [ -n "$lost" ]; then
  echo "LOST (matched before):"; echo "$lost" | sed 's/^/  /'
  exit 1
fi
exit 0
