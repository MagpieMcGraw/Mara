#!/usr/bin/env bash
# `mara ask` goldens. Runs every query in ask_queries.txt and compares the
# combined output with ask_expected.txt.
#
#   test/ask.sh      compare (prints the diff and exits 1 on any change); then
#                    the same queries through `mara serve`, which must answer
#                    each as `mara ask` did, and the fixtures' through a
#                    window (the stand-in test/view_hub): `mara ask` asks it.
#                    Then one serve moved between modules, one window asked
#                    from several, and files that share a name
#   test/ask.sh -u   re-record ask_expected.txt
#
# A query line is `<target> | <args>`. The target is a directory relative to
# the repo root (the query runs there), or a single-file fixture (`test/x.mara`),
# which is copied into a directory named after it, since `mara ask` analyzes
# the module named by its working directory.
ROOT=$(cd "$(dirname "$0")/.." && pwd)
MARA=${MARA:-${MARA_EXE:-$ROOT/mara_dev.exe}}   # (the debug build) another to compare: MARA=... test/ask.sh
[ -x "$MARA" ] || [ -n "${MARA_EXE:-}" ] || MARA=$ROOT/mara_dev   # (built as mara_dev, off Windows)
QUERIES=$ROOT/test/ask_queries.txt
EXPECTED=$ROOT/test/ask_expected.txt
WORK=${TMP:-/tmp}/mara_ask
rm -rf "$WORK"; mkdir -p "$WORK"
# A file outside the module asked about (the stdlib's) prints as a whole
# path: its root made <root>, its separators '/', so the goldens hold on any
# machine.
ROOT_NATIVE=$ROOT
command -v cygpath > /dev/null && ROOT_NATIVE=$(cygpath -w "$ROOT")
export ROOT ROOT_NATIVE
norm_paths() {
  perl -pe 's{(?:\Q$ENV{ROOT_NATIVE}\E|\Q$ENV{ROOT}\E)((?:[\\/][\w.-]+)+)}{my $p = $1; $p =~ tr|\\|/|; "<root>$p"}ge'
}
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
  ( cd "$dir" && "$MARA" ask $args 2>&1 ) | tr -d '\r' | norm_paths >> "$actual"
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
  done < <(printf '%s\n' "${argss[@]:$i:$((j-i))}" | ( cd "${dirs[$i]}" && "$MARA" serve 2>&1 ) | tr -d '\r' | norm_paths)
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
      ( cd "$d" && "$MARA" ask $show ${argss[$k]} 2>&1 ) | tr -d '\r' | norm_paths >> "$routed"
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

# One `mara serve` moved between the fixtures' modules by its queries' -in, twice
# round: the same answers again, each from its own folder.
native() { if command -v cygpath > /dev/null; then cygpath -w "$1"; else echo "$1"; fi; }
moved=$WORK/moved.txt
moved_lines=$WORK/moved_lines.txt
: > "$moved"
: > "$moved_lines"
moved_heads=()
for pass in 1 2; do
  for ((k = 0; k < ${#targets[@]}; k++)); do
    [[ ${targets[$k]} == *.mara ]] || continue
    printf -- '-in "%s" %s %s\n' "$(native "${dirs[$k]}")" "$(basename "${targets[$k]}" .mara)" "${argss[$k]}" >> "$moved_lines"
    moved_heads+=("=== ${targets[$k]} | ${argss[$k]}")
  done
done
k=0
echo "${moved_heads[0]}" >> "$moved"
while IFS= read -r l; do
  if [ "${l#-- end of answer}" != "$l" ]; then
    [ "$l" = "-- end of answer: failed --" ] && echo "[exit 1]" >> "$moved"
    k=$((k+1))
    [ $k -lt ${#moved_heads[@]} ] && echo "${moved_heads[$k]}" >> "$moved"
  else
    echo "$l" >> "$moved"
  fi
done < <( ( cd "$WORK" && "$MARA" serve < "$moved_lines" 2>&1 ) | tr -d '\r' | norm_paths)
cat "$WORK/route_expected.txt" "$WORK/route_expected.txt" > "$WORK/moved_expected.txt"
moved_ok=yes
diff -u "$WORK/moved_expected.txt" "$moved" > "$WORK/moved.diff" || moved_ok=no

# One window, opened on one module, asked from another and back: each gets its
# own module's answer, from the one serve. A folder with no module isn't asked
# of it. `mara view` again, from the other module, doesn't open a second.
follow_problems=""
first=""; second=""
for ((k = 0; k < ${#targets[@]}; k++)); do
  [[ ${targets[$k]} == *.mara ]] || continue
  if [ -z "$first" ]; then first=$k
  elif [ "${targets[$k]}" != "${targets[$first]}" ]; then second=$k; break
  fi
done
d1=${dirs[$first]}; d2=${dirs[$second]}
want1=$(cd "$d1" && "$MARA" ask ${argss[$first]} 2>&1)
want2=$(cd "$d2" && "$MARA" ask ${argss[$second]} 2>&1)
rm -f "$d1/view_hub.log"
( cd "$d1" && MARA_VIEW="$HUB" "$MARA" view ) || follow_problems+="no window opened; "
for t in $(seq 1 100); do [ -f "$d1/view_hub.log" ] && break; sleep 0.1; done
got=$(cd "$d2" && "$MARA" ask -show ${argss[$second]} 2>&1)
[ "$got" = "$want2" ] || follow_problems+="asked from another module, it didn't answer for that module; "
got=$(cd "$d1" && "$MARA" ask -cursor ${argss[$first]} 2>&1)
[ "$got" = "$want1" ] || follow_problems+="asked back from the first module, it didn't answer for it; "
no_module=$WORK/no_module_here
mkdir -p "$no_module"
got=$(cd "$no_module" && "$MARA" ask anything 2>&1)
case $got in *"no Mara module"*) ;; *) follow_problems+="a folder with no module didn't get ask's own answer: $got; " ;; esac
( cd "$d2" && MARA_VIEW="$HUB" "$MARA" view ) || follow_problems+="mara view with one open failed; "
for t in $(seq 1 100); do grep -qs '^ended' "$d1/view_hub.log" && break; sleep 0.1; done
asked=$(grep -cs '^asked: ' "$d1/view_hub.log")
[ "$asked" = 3 ] || follow_problems+="the window was asked $asked times, not 3; "
started=$(grep -cs '^serve started' "$d1/view_hub.log")
[ "$started" = 1 ] || follow_problems+="the window started serve $started times, not 1; "

# A file's name alone can be several files: `at` means the one here. Our own
# time.mara over the stdlib's, and the stdlib's from its own folder, where the
# folder can't say which module (code/) or can (code/os/, its os.mara).
clash=$WORK/clash
mkdir -p "$clash"
printf 'module clash\n\nmain :: fun() {\n\tmine := 1\n\tprint(mine)\n}\n' > "$clash/time.mara"
got=$(cd "$clash" && "$MARA" ask what at time.mara:4:2 2>&1)
case $got in mine$'\n'*) ;; *) follow_problems+="at time.mara in a module with its own wasn't that one: $got; " ;; esac
line=$(grep -n '^clock_ns ::' "$ROOT/code/time.mara" | cut -d: -f1 | head -1)
got=$(cd "$ROOT/code" && "$MARA" ask what at time.mara:$line:1 2>&1)
case $got in "clock_ns — fun"*) ;; *) follow_problems+="at time.mara in code/ didn't find it: $got; " ;; esac
line=$(grep -n '^read_cstring ::' "$ROOT/code/os/os.mara" | cut -d: -f1 | head -1)
got=$(cd "$ROOT/code/os" && "$MARA" ask what at os.mara:$line:1 2>&1)
case $got in "read_cstring — fun"*) ;; *) follow_problems+="at os.mara in code/os/ didn't find it: $got; " ;; esac

serve_ok=yes
# A module in a folder a build.mara names is the project's, in the module map and to a
# shape asked about, though its path is whole; the stdlib's still isn't. And a whole
# path can say where to ask. (In the work folder: no build.mara goes in test/.)
dirs_problems=""
dirs_app=$WORK/dirs_check/app
dirs_shared=$WORK/dirs_check/shared
mkdir -p "$dirs_app" "$dirs_shared"
cat > "$dirs_app/build.mara" <<'MARA'
module build

use mara.build

app :: Build(){dirs = ["../shared"]}
MARA
cat > "$dirs_app/app.mara" <<'MARA'
module app

use mara.core
use shared_part

main :: fun() {
	h := Holder()
	print(h.items.len)
}
MARA
cat > "$dirs_shared/shared_part.mara" <<'MARA'
module shared_part

Holder :: struct {
	items: [16]i64
}
MARA
dirs_map=$(cd "$dirs_app" && "$MARA" ask 2>&1 | tr -d '')
dirs_group() { printf '%s
' "$dirs_map" | awk -v m="$1" '/^  your code/{g="your code"} /^  stdlib/{g="stdlib"} $1==m{print g}'; }
[ "$(dirs_group shared_part)" = "your code" ] || dirs_problems+="shared_part is '$(dirs_group shared_part)' in the map; "
[ "$(dirs_group mara.core)" = "stdlib" ] || dirs_problems+="mara.core is '$(dirs_group mara.core)' in the map; "
( cd "$dirs_app" && "$MARA" ask '[16]i64' 2>&1 ) | grep -q '1 declared' || dirs_problems+="the shape wasn't found; "
dirs_whole=$dirs_shared/shared_part.mara
command -v cygpath > /dev/null && dirs_whole=$(cygpath -w "$dirs_whole")
( cd "$dirs_app" && "$MARA" ask what at "$dirs_whole:4:2" 2>&1 ) | head -1 | grep -q '^items' || dirs_problems+="a whole path wasn't a place to ask; "

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
if [ $moved_ok = yes ]; then
  echo "MOVED: the same answers, one serve going between modules"
else
  cat "$WORK/moved.diff"; echo "MOVED: DIFFERENT (ask's above, the moved serve's below)"; exit 1
fi
if [ -z "$follow_problems" ]; then
  echo "FOLLOW: one window answers for each module"
else
  echo "FOLLOW: $follow_problems"; exit 1
fi
if [ -z "$dirs_problems" ]; then
  echo "DIRS: a folder build.mara names is the project's"
else
  echo "DIRS: $dirs_problems"; exit 1
fi
