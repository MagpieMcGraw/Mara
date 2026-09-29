#!/usr/bin/env bash
# Graph differential. Builds every fixture with a main, the multifile
# fixtures, Pounce and design/all with the baseline compiler
# (Mara_base_tmp.exe at the repo root) and the working one (Mara.exe), each
# dumping its program graph whole (MARA_GRAPH=full: every column of every
# node, the edges, runs, statements and tables), and requires the dumps to be
# identical. The check for a change to how the graph is built that must not
# change the graph.
#
#   test/graphdiff.sh       dumps must be identical
#   test/graphdiff.sh -j N  N programs at a time (default: every core)
#
# The dumps are kept under $OUT/old and $OUT/new; a program whose build
# failed has no dump (its build output is compared instead).
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=${OUT:-${TMP:-/tmp}/mara_graphdiff}
JOBS=$(nproc 2>/dev/null || echo 4)
while [ $# -gt 0 ]; do
  case $1 in
    -j) JOBS=$2; shift ;;
  esac
  shift
done
BASE=$ROOT/Mara_base_tmp.exe WORK=$ROOT/Mara.exe
[ -f "$BASE" ] || { echo "no baseline: copy Mara.exe to Mara_base_tmp.exe first"; exit 2; }
rm -rf "$OUT"; mkdir -p "$OUT/old" "$OUT/new"
export ROOT OUT BASE WORK

# One program, both sides, one after the other (they share the build
# directory): its dump and the checker's diagnostics (a link or clang
# failure — a Windows virus scan holding the exe — is no graph's).
one_program() {  # dir module [build flags]
  local dir=$1 mod=$2 flags=$3 side exe
  for side in old new; do
    exe=$BASE; [ $side = new ] && exe=$WORK
    ( cd "$dir" && { rm -rf "${mod}_build" 2>/dev/null; MARA_GRAPH=full "$exe" build "$mod" $flags 2>&1; } ) \
      | grep -E '^(graph:|n |e |r |s |u |settled |scope |\[)' | grep -v 'is ambiguous (defined in' > "$OUT/$side/$mod.dump"
  done
  rm -rf "$dir/${mod}_build" "$dir/$mod.exe" 2>/dev/null
}
export -f one_program

list=$OUT/programs.txt
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

n=$(ls "$OUT/old" | wc -l)
if diff -r "$OUT/old" "$OUT/new" > "$OUT/diff.txt"; then
  echo "GRAPHDIFF: identical ($n programs)"
  exit 0
fi
echo "GRAPHDIFF: DIFFERENCES"
diff -r --brief "$OUT/old" "$OUT/new" | head -30
exit 1
