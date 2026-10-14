#!/usr/bin/env bash
# `mara ask` goldens. Runs every query in ask_queries.txt and compares the
# combined output with ask_expected.txt.
#
#   test/ask.sh      compare (prints the diff and exits 1 on any change); then
#                    the same queries through `mara serve`, which must answer
#                    each as `mara ask` did, and the fixtures' through a
#                    window (the stand-in test/view_hub): `mara ask` asks it
#   test/ask.sh -u   re-record ask_expected.txt
#
# A query line is `<target> | <args>`. The target is a directory relative to
# the repo root (the query runs there), or a single-file fixture (`test/x.mara`),
# which is copied into a directory named after it, since `mara ask` analyzes
# the module named by its working directory.
ROOT=$(cd "$(dirname "$0")/.." && pwd)
MARA=${MARA:-${MARA_EXE:-$ROOT/mara_dev.exe}}   # (the debug build) another to compare: MARA=... test/ask.sh
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
  [ ${PIPESTATUS[0]} -ne 0 ] && echo "[exit 1]" >> "$actual"   # (a failure: recorded, as serve's end line says it)
  targets+=("$target"); argss+=("$args"); dirs+=("$dir")
done < "$QUERIES"

# The same queries through `mara serve`: each run of one target's queries to
# one server, its answers split at their end lines — '-- end of answer --',
# or '-- end of answer: failed --', which `mara ask` exits 1 on.
served=$WORK/served.txt
: > "$served"
i=0
while [ $i -lt ${#targets[@]} ]; do
  j=$i
  while [ $j -lt ${#targets[@]} ] && [ "${targets[$j]}" = "${targets[$i]}" ]; do j=$((j+1)); done
  k=$i
  echo "=== ${targets[$k]} | ${argss[$k]}" >> "$served"
  while IFS= read -r l; do
    if [ "${l#-- end of answer}" != "$l" ]; then
      [ "$l" = "-- end of answer: failed --" ] && echo "[exit 1]" >> "$served"
      k=$((k+1))
      [ $k -lt $j ] && echo "=== ${targets[$k]} | ${argss[$k]}" >> "$served"
    else
      echo "$l" >> "$served"
    fi
  done < <(printf '%s\n' "${argss[@]:$i:$((j-i))}" | ( cd "${dirs[$i]}" && "$MARA" serve 2>&1 ) | tr -d '\r')
  i=$j
done
# The fixtures' queries through a window: the stand-in test/view_hub, started
# by `mara view` (MARA_VIEW naming it) where each copied fixture is, so that
# `mara ask` there asks it — the same answers again, and in its log, each.
# Every other one is asked with -show (a query the window shows): the same
# answer.
# Before askat's third, its serve is ended, as a crash would: the window
# starts another, and answers on.
kill_serve() {  # module: its window's `mara serve` ended
  if command -v powershell.exe > /dev/null; then
    powershell.exe -NoProfile -Command "Get-CimInstance Win32_Process | Where-Object { \$_.CommandLine -like '*serve $1' } | ForEach-Object { Stop-Process -Id \$_.ProcessId -Force }" > /dev/null
  else
    pkill -f "serve $1\$"
  fi
}
hub_dir=$WORK/view_hub
mkdir -p "$hub_dir" && cp "$ROOT/test/view_hub/view_hub.mara" "$hub_dir/"
( cd "$hub_dir" && "$MARA" build view_hub > /dev/null 2>&1 )
HUB=$hub_dir/view_hub; [ -f "$HUB.exe" ] && HUB=$HUB.exe
command -v cygpath > /dev/null && HUB=$(cygpath -w "$HUB")   # (Windows starts it)
routed=$WORK/routed.txt
: > "$routed"
route_problems=""
i=0
while [ $i -lt ${#targets[@]} ]; do
  j=$i
  while [ $j -lt ${#targets[@]} ] && [ "${targets[$j]}" = "${targets[$i]}" ]; do j=$((j+1)); done
  if [[ ${targets[$i]} == *.mara ]]; then   # (a copy's directory: its log can go there)
    d=${dirs[$i]}
    rm -f "$d/view_hub.log"
    ( cd "$d" && MARA_VIEW="$HUB" "$MARA" view ) || route_problems+="no window opened for ${targets[$i]}; "
    for t in $(seq 1 100); do [ -f "$d/view_hub.log" ] && break; sleep 0.1; done   # (listening)
    for ((k = i; k < j; k++)); do
      if [ "${targets[$k]}" = test/askat.mara ] && [ $k -eq $((i + 2)) ]; then
        kill_serve askat; sleep 0.5
      fi
      echo "=== ${targets[$k]} | ${argss[$k]}" >> "$routed"
      show=""; [ $(( (k - i) % 2 )) -eq 1 ] && show=-show
      ( cd "$d" && "$MARA" ask $show ${argss[$k]} 2>&1 ) | tr -d '\r' >> "$routed"
      [ ${PIPESTATUS[0]} -ne 0 ] && echo "[exit 1]" >> "$routed"
    done
    for t in $(seq 1 100); do grep -qs '^ended' "$d/view_hub.log" && break; sleep 0.1; done
    asked=$(grep -cs '^asked: ' "$d/view_hub.log")
    [ "$asked" = $((j - i)) ] || route_problems+="the window for ${targets[$i]} answered $asked of $((j - i)); "
    started=$(grep -cs '^serve started' "$d/view_hub.log")
    want=1; [ "${targets[$i]}" = test/askat.mara ] && want=2
    [ "$started" = $want ] || route_problems+="the window for ${targets[$i]} started serve $started times, not $want; "
  fi
  i=$j
done
awk '/^=== /{keep = ($2 ~ /\.mara$/)} keep' "$actual" > "$WORK/route_expected.txt"
route_ok=yes
if ! diff -u "$WORK/route_expected.txt" "$routed" > "$WORK/route.diff" || [ -n "$route_problems" ]; then
  route_ok=no
fi

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
if [ $route_ok = yes ]; then
  echo "ROUTE: the same answers, through a window"
else
  cat "$WORK/route.diff"; echo "$route_problems"; echo "ROUTE: DIFFERENT (ask's above, the window's below)"; exit 1
fi
