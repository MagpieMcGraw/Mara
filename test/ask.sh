#!/usr/bin/env bash
# `mara ask` goldens. Runs every query in ask_queries.txt and compares the
# combined output with ask_expected.txt.
#
#   test/ask.sh      compare (prints the diff and exits 1 on any change); then
#                    the same queries through `mara serve`, which must answer
#                    each as `mara ask` did
#   test/ask.sh -u   re-record ask_expected.txt
#
# A query line is `<target> | <args>`. The target is a directory relative to
# the repo root (the query runs there), or a single-file fixture (`test/x.mara`),
# which is copied into a directory named after it, since `mara ask` analyzes
# the module named by its working directory.
ROOT=$(cd "$(dirname "$0")/.." && pwd)
MARA=${MARA:-$ROOT/Mara.exe}   # another compiler to compare: MARA=... test/ask.sh
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
  targets+=("$target"); argss+=("$args"); dirs+=("$dir")
done < "$QUERIES"

# The same queries through `mara serve`: each run of one target's queries to
# one server, its answers split at '-- end of answer --'.
served=$WORK/served.txt
: > "$served"
i=0
while [ $i -lt ${#targets[@]} ]; do
  j=$i
  while [ $j -lt ${#targets[@]} ] && [ "${targets[$j]}" = "${targets[$i]}" ]; do j=$((j+1)); done
  k=$i
  echo "=== ${targets[$k]} | ${argss[$k]}" >> "$served"
  while IFS= read -r l; do
    if [ "$l" = "-- end of answer --" ]; then
      k=$((k+1))
      [ $k -lt $j ] && echo "=== ${targets[$k]} | ${argss[$k]}" >> "$served"
    else
      echo "$l" >> "$served"
    fi
  done < <(printf '%s\n' "${argss[@]:$i:$((j-i))}" | ( cd "${dirs[$i]}" && "$MARA" serve 2>&1 ) | tr -d '\r')
  i=$j
done
serve_ok=yes
if ! diff -u "$actual" "$served" > "$WORK/serve.diff"; then
  serve_ok=no
fi

if [ "$1" = "-u" ]; then
  cp "$actual" "$EXPECTED"
  echo "ASK: recorded $(grep -c '^=== ' "$actual") queries"
elif diff -u <(tr -d '\r' < "$EXPECTED") "$actual"; then   # (a checkout's CRLF aside)
  echo "ASK: $(grep -c '^=== ' "$actual") queries match"
else
  echo "ASK: DIFFERENCES"; exit 1
fi
if [ $serve_ok = yes ]; then
  echo "SERVE: the same answers"
else
  cat "$WORK/serve.diff"; echo "SERVE: DIFFERENT ANSWERS (ask's above, serve's below)"; exit 1
fi
