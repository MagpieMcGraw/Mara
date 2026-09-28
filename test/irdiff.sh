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
#
# Build output (diagnostics, minus timings) must match either way. Both sides
# are kept under $OUT for inspection.
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=${OUT:-${TMP:-/tmp}/mara_irdiff}
NORMALIZE=0
RUN=0
GRAPH=0
OLD_ONLY=0
for a in "$@"; do
  case $a in
    -n) NORMALIZE=1 ;;
    -r) RUN=1 ;;
    -g) GRAPH=1 ;;
    -o) OLD_ONLY=1 ;;
  esac
done
OLD=$ROOT/Mara_base_tmp.exe OLD_CG=1
[ $GRAPH = 1 ] && OLD=$ROOT/Mara.exe OLD_CG=0
[ -f "$OLD" ] || { echo "no baseline: copy Mara.exe to Mara_base_tmp.exe first"; exit 2; }
rm -rf "$OUT"; mkdir -p "$OUT/old" "$OUT/new" "$OUT/run/old" "$OUT/run/new"
RUNS=()   # "dir module" of each program to run
unset MARA_AST_SHAPE

build_both() {  # dir module
  local dir=$1 mod=$2
  for side in old new; do
    local exe=$OLD cg=$OLD_CG
    [ $side = new ] && exe=$ROOT/Mara.exe cg=$((1 - OLD_ONLY))
    ( cd "$dir" && rm -rf "${mod}_build" "$mod.exe" && MARA_GRAPH_CG=$cg "$exe" build "$mod" 2>&1 ) \
      | grep -vE '[0-9]+(\.[0-9]+)?ms|Purity quotient|is ambiguous \(defined in' \
      | sort > "$OUT/$side/$mod.out"   # diagnostics order follows map iteration
    if [ -d "$dir/${mod}_build" ]; then
      mkdir -p "$OUT/$side/$mod"
      cp "$dir/${mod}_build"/*.ll "$OUT/$side/$mod/" 2>/dev/null
    fi
    [ -f "$dir/$mod.exe" ] && cp "$dir/$mod.exe" "$OUT/run/$side/$mod.exe"
  done
}

cd "$ROOT/test"
for f in *.mara; do
  n=${f%.mara}
  grep -qE '^[[:space:]]*main[[:space:]]*::' "$f" || continue
  build_both "$ROOT/test" "$n"
  RUNS+=("$ROOT/test $n")
done
for d in "$ROOT"/test/*/; do
  d=${d%/}; [ -f "$d/.multifile" ] || continue
  build_both "$d" "$(basename "$d")"
  RUNS+=("$d $(basename "$d")")
done
build_both "$ROOT/Pounce" Pounce
build_both "$ROOT/design" all

status=0
builds=$(ls "$OUT/old" | grep -c '\.out$')
if [ $NORMALIZE = 1 ]; then
  for f in $(cd "$OUT/old" && find . -name '*.ll'); do
    [ -f "$OUT/new/$f" ] || continue
    perl "$ROOT/test/irnorm.pl" "$OUT/old/$f" > "$OUT/old/$f.norm"
    perl "$ROOT/test/irnorm.pl" "$OUT/new/$f" > "$OUT/new/$f.norm"
  done
  if diff -r -x '*.ll' "$OUT/old" "$OUT/new" > "$OUT/diff.txt"; then
    echo "IRDIFF: identical modulo naming ($builds builds)"
  else
    echo "IRDIFF: DIFFERENCES"; diff -r -x '*.ll' --brief "$OUT/old" "$OUT/new" | head -30; status=1
  fi
else
  if diff -r "$OUT/old" "$OUT/new" > "$OUT/diff.txt"; then
    echo "IRDIFF: identical ($builds builds)"
  else
    echo "IRDIFF: DIFFERENCES"; diff -r --brief "$OUT/old" "$OUT/new" | head -30; status=1
  fi
fi

# The runtime differential: each program both sides built, run from its
# directory; its output and exit code must match.
if [ $RUN = 1 ]; then
  ran=0; differ=0
  for entry in "${RUNS[@]}"; do
    dir=${entry% *}; mod=${entry##* }
    [ -f "$OUT/run/old/$mod.exe" ] && [ -f "$OUT/run/new/$mod.exe" ] || continue
    for side in old new; do
      ( cd "$dir" && timeout 10 "$OUT/run/$side/$mod.exe" > "$OUT/run/$side/$mod.run" 2>&1
        echo "exit $?" >> "$OUT/run/$side/$mod.run" )
    done
    ran=$((ran+1))
    if ! cmp -s "$OUT/run/old/$mod.run" "$OUT/run/new/$mod.run"; then
      differ=$((differ+1)); echo "  runs differ: $mod"
    fi
  done
  if [ $differ = 0 ]; then
    echo "RUNDIFF: identical ($ran programs)"
  else
    echo "RUNDIFF: $differ of $ran programs differ"; status=1
  fi
fi
exit $status
