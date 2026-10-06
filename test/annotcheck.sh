#!/usr/bin/env bash
# The annotations' check (design/annotated_tree.md, stage 1). Builds every
# fixture with a main, the multifile fixtures, Pounce and design/all with
# MARA_ANNOT=check: each program's annotations must be complete and agree with
# its program graph. Lists each problem; exits 1 when there is any.
#
#   test/annotcheck.sh       every program
#   test/annotcheck.sh -j N  N programs at a time (default: every core)
#
# Each program's problems are kept under $OUT.
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=${OUT:-${TMP:-/tmp}/mara_annotcheck}
JOBS=$(nproc 2>/dev/null || echo 4)
while [ $# -gt 0 ]; do
  case $1 in
    -j) JOBS=$2; shift ;;
  esac
  shift
done
WORK=$ROOT/Mara.exe
rm -rf "$OUT"; mkdir -p "$OUT"
export ROOT OUT WORK

one_program() {  # dir module [build flags]
  local dir=$1 mod=$2 flags=$3
  ( cd "$dir" && { rm -rf "${mod}_build" 2>/dev/null; MARA_ANNOT=check "$WORK" build "$mod" $flags 2>&1; } ) \
    | grep -E '^annot: ' > "$OUT/$mod.txt"
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

n=$(wc -l < "$list")
checked=$(grep -l '^annot: [0-9]* problems' "$OUT"/*.txt 2>/dev/null | wc -l)
totals=$(grep -h '^annot: [0-9]* problems' "$OUT"/*.txt | awk -F'[(, ]+' '{ n += $4; v += $6; c += $8; g += $10; l += $13; d += $20 } END { printf "%d names, %d variables, %d calls, %d arguments; %d loop variables written by their loop; %d declarations", n, v, c, g, l, d }')
problems=$(grep -h -v '^annot: [0-9]* problems' "$OUT"/*.txt 2>/dev/null)
count=$(printf '%s' "$problems" | grep -c . )
if [ "$count" -eq 0 ]; then
  echo "ANNOT: complete and agreeing ($totals in $checked of $n programs; the rest have errors)"
  exit 0
fi
printf '%s\n' "$problems" | head -40
echo "ANNOT: $count problems ($checked of $n programs checked)"
exit 1
