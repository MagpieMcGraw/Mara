#!/usr/bin/env bash
# The resolver's check (design/name_resolution.md, stage 1). Builds every
# fixture with a main, the multifile fixtures, Pounce and design/all with
# MARA_RESOLVE=check (no link: the check is all it's for): each name the
# resolver resolved is compared with the ref the checker recorded. Lists the
# disagreements, then the counts by kind summed over the programs.
#
#   test/resolvecheck.sh       every program
#   test/resolvecheck.sh -j N  N programs at a time (default: every core)
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=${OUT:-${TMP:-/tmp}/mara_resolvecheck}
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
  ( cd "$dir" && { rm -rf "${mod}_build" 2>/dev/null; MARA_RESOLVE=check MARA_NO_LINK=1 MARA_LLVM=1 "$WORK" build "$mod" $flags 2>&1; } ) \
    | grep -E '^resolve: |\.odin\([0-9]+:[0-9]+\)|^Found [0-9]+ .*error' > "$OUT/$mod.txt"
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
checked=$(grep -l '^resolve: [0-9]* agree' "$OUT"/*.txt 2>/dev/null | wc -l)
# (Each disagreement once: the stdlib's are every program's.)
grep -h '^resolve: .*: checker .*, resolver ' "$OUT"/*.txt | grep -v '^resolve: \(differ\|only-checker\|only-resolver\|dispatch\|holds\) ' | sort -u | head -80
echo "--- by kind, summed over the programs"
grep -h '^resolve: \(differ\|only-checker\|only-resolver\|dispatch\|holds\) ' "$OUT"/*.txt   | awk -F': ' '{ sum[$2 ": " $3] += $4 } END { for (k in sum) print sum[k] "	" k }' | sort -t$'	' -k2
grep -h '^resolve: [0-9]* agree' "$OUT"/*.txt | awk '{ a += $2; d += $4; c += $6; r += $10; p += $14; h += $18 } END { printf "RESOLVE: %d agree, %d differ, %d only the checker'"'"'s, %d only the resolver'"'"'s, %d a dispatch'"'"'s member, %d what a variable holds", a, d, c, r, p, h }'
echo " ($checked of $n programs checked; the rest have errors)"
# (Each lookup the checker made: its scope's answer against the name's ref and binding.)
grep -h '^resolve: lookup ' "$OUT"/*.txt | sort -u | head -40
grep -h '^resolve: lookups: ' "$OUT"/*.txt | awk '{ a += $3; d += $5; n += $7 } END { printf "LOOKUPS: %d agree, %d differ, %d no ref\n", a, d, n }'
# (A program neither checked nor with errors: the resolver crashed on it.)
crashed=$(for f in "$OUT"/*.txt; do grep -q '^resolve: [0-9]* agree\|^Found [0-9]' "$f" || basename "$f" .txt; done)
if [ -n "$crashed" ]; then echo "RESOLVE: no result for: $crashed"; grep -h '\.odin([0-9]*:[0-9]*)' "$OUT"/*.txt | sort -u | head; exit 1; fi
