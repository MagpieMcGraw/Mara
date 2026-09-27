#!/usr/bin/env bash
# `mara ask` goldens. Runs every query in ask_queries.txt and compares the
# combined output with ask_expected.txt.
#
#   test/ask.sh      compare (prints the diff and exits 1 on any change)
#   test/ask.sh -u   re-record ask_expected.txt
#
# A query line is `<target> | <args>`. The target is a directory relative to
# the repo root (the query runs there), or a single-file fixture (`test/x.mara`),
# which is copied into a directory named after it, since `mara ask` analyzes
# the module named by its working directory.
ROOT=$(cd "$(dirname "$0")/.." && pwd)
MARA=$ROOT/Mara.exe
QUERIES=$ROOT/test/ask_queries.txt
EXPECTED=$ROOT/test/ask_expected.txt
WORK=${TMP:-/tmp}/mara_ask
rm -rf "$WORK"; mkdir -p "$WORK"
actual=$WORK/actual.txt
: > "$actual"

while IFS= read -r line || [ -n "$line" ]; do
  line=${line%$'\r'}
  case $line in ''|'#'*) continue ;; esac
  target=$(echo "${line%%|*}" | xargs)
  args=$(echo "${line#*|}" | xargs)
  if [[ $target == *.mara ]]; then
    mod=$(basename "$target" .mara)
    dir=$WORK/$mod
    mkdir -p "$dir" && cp "$ROOT/$target" "$dir/"
  else
    dir=$ROOT/$target
  fi
  echo "=== $target | $args" >> "$actual"
  ( cd "$dir" && "$MARA" ask $args 2>&1 ) | tr -d '\r' >> "$actual"
done < "$QUERIES"

if [ "$1" = "-u" ]; then
  cp "$actual" "$EXPECTED"
  echo "ASK: recorded $(grep -c '^=== ' "$actual") queries"
elif diff -u "$EXPECTED" "$actual"; then
  echo "ASK: $(grep -c '^=== ' "$actual") queries match"
else
  echo "ASK: DIFFERENCES"; exit 1
fi
