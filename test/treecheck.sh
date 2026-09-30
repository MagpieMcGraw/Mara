#!/usr/bin/env bash
# treecheck.sh — the flat tree (design/flat_tree.md) loses nothing: every
# fixture, multi-file fixture, Pounce and design/all parsed into it beside the
# pointer tree under MARA_TREE=check, which checks the tree (tree_check) and
# that a file one parser rejects the other rejects too. Prints each failure's
# report and a count.
#
#   test/treecheck.sh          every program
#   test/treecheck.sh -j N     N at a time (default: every core)
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
EXE="$ROOT/Mara.exe"
JOBS=$(nproc 2>/dev/null || echo 4)
[ "$1" = -j ] && JOBS=$2
OUT=$(mktemp -d)
export EXE OUT

one() {  # dir module
  local dir=$1 mod=$2 out rc
  out=$(cd "$dir" && MARA_TREE=check timeout 120 "$EXE" build "$mod" 2>&1)
  rc=$?
  # (A file no build parses — a multi-file module's part — is no program.)
  echo "$out" | grep -qE "^tree:" || { echo "$dir $mod" >> "$OUT/skipped"; return; }
  if [ $rc -ne 0 ]; then
    { echo "== $dir $mod"; echo "$out" | grep -E "tree( parse error)?:|^tree:" | head -20; } > "$OUT/$(basename "$dir")_$mod.fail"
  fi
  echo "$out" | grep -E "^tree:" >> "$OUT/summaries"
}
export -f one

list=$OUT/programs.txt
: > "$list"
cd "$ROOT/test"
for f in *.mara; do echo "$ROOT/test ${f%.mara}" >> "$list"; done
for d in "$ROOT"/test/*/; do
  d=${d%/}; [ -f "$d/.multifile" ] && echo "$d $(basename "$d")" >> "$list"
done
echo "$ROOT/Pounce Pounce" >> "$list"
echo "$ROOT/design all" >> "$list"
xargs -P "$JOBS" -L 1 bash -c 'one "$0" "$1"' < "$list"

skipped=$(cat "$OUT/skipped" 2>/dev/null | wc -l)
n=$(($(wc -l < "$list") - skipped))
fails=$(ls "$OUT"/*.fail 2>/dev/null | wc -l)
cat "$OUT"/*.fail 2>/dev/null
nodes=$(awk '{ for (i = 1; i <= NF; i++) if ($(i+1) == "nodes,") s += $i } END { print s + 0 }' "$OUT/summaries" 2>/dev/null)
rm -rf "$OUT"
if [ "$fails" -eq 0 ]; then
  echo "TREECHECK: all $n programs lose nothing ($nodes nodes; $skipped files no build parses)"
else
  echo "TREECHECK: $fails of $n programs failed"
  exit 1
fi
