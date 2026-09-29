#!/usr/bin/env bash
# IR differential. Builds every fixture with a main, the multifile fixtures,
# Pounce and design/all with a baseline compiler and with the working one
# (Mara.exe), then compares the two. The baseline is Mara_base_tmp.exe at the
# repo root: copy Mara.exe there at the commit you compare against.
#
#   test/irdiff.sh      IR must be byte-identical
#   test/irdiff.sh -n   IR must match modulo naming (see irnorm.pl): locals,
#                       labels and string-global names, and what can't change
#                       behavior (the rules are listed in irnorm.pl)
#   test/irdiff.sh -r   also run every fixture both builds made, and compare
#                       output and exit code (the runtime differential)
#   test/irdiff.sh -g   compare the working compiler's two emitters instead of
#                       two compilers: Mara.exe with MARA_GRAPH_CG=0 (the
#                       syntax-tree emitter) against Mara.exe (the graph's,
#                       for every fun it lowers)
#   test/irdiff.sh -o   run the working compiler with the graph emitter off
#                       (MARA_GRAPH_CG=0): what changed in the old one
#   test/irdiff.sh -a   both of those in one pass, three builds of each
#                       program — the baseline (base), Mara.exe with the graph
#                       emitter off (off) and on (on): base against off must
#                       run the same (their IR differences are listed, not
#                       failed: that is where the old emitter changes), off
#                       against on is the -g check
#   test/irdiff.sh -j N N programs at a time (default: every core)
#
# Build output (diagnostics, minus timings) must match either way. Every side
# is kept under $OUT for inspection: $OUT/old and $OUT/new, or with -a
# $OUT/base, $OUT/off and $OUT/on.
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=${OUT:-${TMP:-/tmp}/mara_irdiff}
NORMALIZE=0 RUN=0 GRAPH=0 OLD_ONLY=0 ALL=0
JOBS=$(nproc 2>/dev/null || echo 4)
while [ $# -gt 0 ]; do
  case $1 in
    -n) NORMALIZE=1 ;;
    -r) RUN=1 ;;
    -g) GRAPH=1 ;;
    -o) OLD_ONLY=1 ;;
    -a) ALL=1 NORMALIZE=1 ;;
    -j) JOBS=$2; shift ;;
  esac
  shift
done
BASE=$ROOT/Mara_base_tmp.exe WORK=$ROOT/Mara.exe
# The sides, each `name:compiler:MARA_GRAPH_CG`, and the pairs compared.
if [ $ALL = 1 ]; then
  SIDES="base:$BASE:1 off:$WORK:0 on:$WORK:1"
elif [ $GRAPH = 1 ]; then
  SIDES="old:$WORK:0 new:$WORK:1"
else
  SIDES="old:$BASE:1 new:$WORK:$((1 - OLD_ONLY))"
fi
[ $GRAPH = 1 ] || [ -f "$BASE" ] || { echo "no baseline: copy Mara.exe to Mara_base_tmp.exe first"; exit 2; }
rm -rf "$OUT"
for s in $SIDES; do mkdir -p "$OUT/${s%%:*}" "$OUT/run/${s%%:*}"; done
unset MARA_AST_SHAPE
export ROOT OUT NORMALIZE RUN SIDES

# One program, every side: built, its IR kept (and normalized), then — a
# program to run — run from its directory, output and exit code kept. The
# sides go one after another (they share the build directory and the exe).
one_program() {  # dir module run [build flags]
  local dir=$1 mod=$2 run=$3 flags=$4 s side exe cg f
  for s in $SIDES; do
    side=${s%%:*}; exe=${s#*:}; exe=${exe%:*}; cg=${s##*:}
    # Windows can hold a fresh exe a moment (a virus scan): retry its removal.
    for t in 1 2 3 4 5; do rm -f "$dir/$mod.exe" 2>/dev/null; [ -e "$dir/$mod.exe" ] || break; sleep 1; done
    ( cd "$dir" && { rm -rf "${mod}_build" "$mod.exe" 2>/dev/null; MARA_GRAPH_CG=$cg "$exe" build "$mod" $flags 2>&1; } ) \
      | grep -vE '[0-9]+(\.[0-9]+)?ms|Purity quotient|is ambiguous \(defined in' \
      | sort > "$OUT/$side/$mod.out"   # diagnostics order follows map iteration
    if [ -d "$dir/${mod}_build" ]; then
      mkdir -p "$OUT/$side/$mod"
      cp "$dir/${mod}_build"/*.ll "$OUT/$side/$mod/" 2>/dev/null
      if [ $NORMALIZE = 1 ]; then
        for f in "$OUT/$side/$mod"/*.ll; do
          [ -f "$f" ] && perl "$ROOT/test/irnorm.pl" "$f" > "$f.norm"
        done
      fi
    fi
    if [ $RUN = 1 ] && [ "$run" = 1 ] && [ -f "$dir/$mod.exe" ]; then
      cp "$dir/$mod.exe" "$OUT/run/$side/$mod.exe"
      ( cd "$dir" && timeout 10 "$OUT/run/$side/$mod.exe" > "$OUT/run/$side/$mod.run" 2>&1
        echo "exit $?" >> "$OUT/run/$side/$mod.run" )
    fi
  done
}
export -f one_program

# The programs: each fixture with a main and each multifile fixture (built
# and run; a .shared one, a DLL, built), Pounce and design/all (built).
list=$OUT/programs.txt
: > "$list"
cd "$ROOT/test"
for f in *.mara; do
  grep -qE '^[[:space:]]*main[[:space:]]*::' "$f" && echo "$ROOT/test ${f%.mara} 1" >> "$list"
done
for d in "$ROOT"/test/*/; do
  d=${d%/}; [ -f "$d/.multifile" ] || continue
  if [ -f "$d/.shared" ]; then echo "$d $(basename "$d") 0 -shared"; else echo "$d $(basename "$d") 1"; fi >> "$list"
done
echo "$ROOT/Pounce Pounce 0" >> "$list"
echo "$ROOT/design all 0" >> "$list"
xargs -P "$JOBS" -L 1 bash -c 'one_program "$0" "$1" "$2" "$3"' < "$list"

# Two sides compared: their builds (output and IR, normalized with -n), then,
# with -r, their runs. `ir_fails` 0 lists IR differences without failing.
status=0
compare() {  # a b ir_fails
  local a=$1 b=$2 ir_fails=$3 builds
  builds=$(ls "$OUT/$a" | grep -c '\.out$')
  local x=(-x run)
  if [ $NORMALIZE = 1 ]; then x+=(-x '*.ll'); else x+=(-x '*.norm'); fi
  if diff -r "${x[@]}" "$OUT/$a" "$OUT/$b" > "$OUT/diff.$a.$b.txt"; then
    if [ $NORMALIZE = 1 ]; then echo "IRDIFF $a/$b: identical modulo naming ($builds builds)"
    else echo "IRDIFF $a/$b: identical ($builds builds)"; fi
  elif [ "$ir_fails" = 1 ]; then
    echo "IRDIFF $a/$b: DIFFERENCES"; diff -r "${x[@]}" --brief "$OUT/$a" "$OUT/$b" | head -30; status=1
  else
    echo "IRDIFF $a/$b: $(diff -r "${x[@]}" --brief "$OUT/$a" "$OUT/$b" | wc -l) files differ (listed in $OUT/diff.$a.$b.txt)"
  fi
  [ $RUN = 1 ] || return
  local ran=0 differ=0 r mod
  for r in "$OUT/run/$a"/*.run; do
    [ -f "$r" ] || continue
    mod=$(basename "$r" .run)
    [ -f "$OUT/run/$b/$mod.run" ] || continue
    ran=$((ran + 1))
    if ! cmp -s "$r" "$OUT/run/$b/$mod.run"; then
      differ=$((differ + 1)); echo "  runs differ: $mod"
    fi
  done
  if [ $differ = 0 ]; then echo "RUNDIFF $a/$b: identical ($ran programs)"
  else echo "RUNDIFF $a/$b: $differ of $ran programs differ"; status=1; fi
}
if [ $ALL = 1 ]; then
  compare base off 0
  compare off on 1
else
  compare old new 1
fi
exit $status
