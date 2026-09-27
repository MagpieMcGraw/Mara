#!/usr/bin/env bash
# IR differential. Builds every fixture with a main, the multifile fixtures,
# Pounce and design/all with a baseline compiler and with the working one
# (Mara.exe), then compares the two. The baseline is Mara_base_tmp.exe at the
# repo root: copy Mara.exe there at the commit you compare against.
#
#   test/irdiff.sh      IR must be byte-identical
#   test/irdiff.sh -n   IR must match modulo naming (see irnorm.pl): locals,
#                       labels and string-global names
#
# Build output (diagnostics, minus timings) must match either way. Both sides
# are kept under $OUT for inspection.
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=${OUT:-${TMP:-/tmp}/mara_irdiff}
NORMALIZE=0
[ "$1" = "-n" ] && NORMALIZE=1
[ -f "$ROOT/Mara_base_tmp.exe" ] || { echo "no baseline: copy Mara.exe to Mara_base_tmp.exe first"; exit 2; }
rm -rf "$OUT"; mkdir -p "$OUT/old" "$OUT/new"
unset MARA_AST_SHAPE

build_both() {  # dir module
  local dir=$1 mod=$2
  for side in old new; do
    local exe=$ROOT/Mara_base_tmp.exe
    [ $side = new ] && exe=$ROOT/Mara.exe
    ( cd "$dir" && rm -rf "${mod}_build" && "$exe" build "$mod" 2>&1 ) \
      | grep -vE '[0-9]+(\.[0-9]+)?ms|Purity quotient|is ambiguous \(defined in' \
      | sort > "$OUT/$side/$mod.out"   # diagnostics order follows map iteration
    if [ -d "$dir/${mod}_build" ]; then
      mkdir -p "$OUT/$side/$mod"
      cp "$dir/${mod}_build"/*.ll "$OUT/$side/$mod/" 2>/dev/null
    fi
  done
}

cd "$ROOT/test"
for f in *.mara; do
  n=${f%.mara}
  grep -qE '^[[:space:]]*main[[:space:]]*::' "$f" || continue
  build_both "$ROOT/test" "$n"
done
for d in "$ROOT"/test/*/; do
  d=${d%/}; [ -f "$d/.multifile" ] || continue
  build_both "$d" "$(basename "$d")"
done
build_both "$ROOT/Pounce" Pounce
build_both "$ROOT/design" all

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
    echo "IRDIFF: DIFFERENCES"; diff -r -x '*.ll' --brief "$OUT/old" "$OUT/new" | head -30; exit 1
  fi
else
  if diff -r "$OUT/old" "$OUT/new" > "$OUT/diff.txt"; then
    echo "IRDIFF: identical ($builds builds)"
  else
    echo "IRDIFF: DIFFERENCES"; diff -r --brief "$OUT/old" "$OUT/new" | head -30; exit 1
  fi
fi
