#!/usr/bin/env bash
# Mara test-fixture runner. Builds every test/*.mara, compares the actual
# outcome to the expected one, and reports ONLY mismatches — real regressions
# and stale fixtures. Exits 1 if any mismatch, so it works as a CI gate.
#
# Expectation, in priority order:
#   1. //@ expect-fail[: substr]  (in the file) — must NOT compile; if a substr
#                                  is given, the error output must contain it.
#   2. //@ expect-skip: reason    (in the file) — skipped.
#   3. the LEGACY lists below      — for fixtures predating the annotation.
#   4. auto-skip                   — build says "no main"/"no files found"
#                                    (a library or one piece of a multi-file test).
#   5. default                     — must compile.
#
# New fixtures should use the //@ annotations; the lists are a migration shim.
# (test/failures/*.mara have no main and can't build standalone — out of scope
#  until `mara` grows a check-only mode.)

cd "$(dirname "$0")" || exit 2
MARA=../Mara.exe

LEGACY_FAIL="capsize_neg clangfail erruse_neg escape_struct_lit_neg fixed_decay_neg inferconflict widenneg"
# name:reason — stale/pre-existing-broken fixtures that DO have a main (so they
# won't auto-skip). Clean these up and the entries go away.
LEGACY_SKIP="font_test:stale-calls-removed-load_glyphs constlit:stale-uses-removed-str constmoduse:stale-multimodule-uses-removed-str leak_consumer:stale-multimodule-uses-removed-Arena_Basic mandelbrot_bench_simd:preexisting-not-applied-to-err"

in_list() { case " $1 " in *" $2 "*) return 0 ;; esac; return 1; }
skip_reason() { for kv in $LEGACY_SKIP; do case "$kv" in "$1:"*) echo "${kv#*:}"; return ;; esac; done; }

pass=0; xfail=0; skip=0; bad=0
for f in *.mara; do
  name="${f%.mara}"
  exp=pass; substr=""
  if grep -qE '//@ expect-fail' "$f" 2>/dev/null; then
    exp=fail
    substr=$(sed -nE 's#.*//@ expect-fail:[[:space:]]*(.+)#\1#p' "$f" | head -1)
  elif grep -qE '//@ expect-skip:' "$f" 2>/dev/null; then
    exp=skip
  elif in_list "$LEGACY_FAIL" "$name"; then
    exp=fail
  elif [ -n "$(skip_reason "$name")" ]; then
    exp=skip
  elif ! grep -qE '^[[:space:]]*main[[:space:]]*::' "$f"; then
    exp=skip
  fi
  [ "$exp" = skip ] && { skip=$((skip+1)); continue; }

  out=$("$MARA" build "$name" 2>&1)
  if echo "$out" | grep -qE "has no .main|no files found"; then skip=$((skip+1)); continue; fi
  comp=no; echo "$out" | grep -q "Compiled module" && comp=yes

  if [ "$exp" = pass ]; then
    if [ "$comp" = yes ]; then pass=$((pass+1)); else echo "REGRESSION (want pass, failed): $name"; bad=$((bad+1)); fi
  else
    if [ "$comp" = yes ]; then echo "STALE NEGATIVE (want fail, compiled): $name"; bad=$((bad+1))
    elif [ -n "$substr" ] && ! echo "$out" | grep -qF "$substr"; then echo "WRONG ERROR: $name (want substring: $substr)"; bad=$((bad+1))
    else xfail=$((xfail+1)); fi
  fi
done

# Multi-file module fixtures (cross-file resolution) live in opt-in subdirs
# marked with a .multifile file. The flat per-file loop above can't combine
# them, and loose multi-file modules collide on discovery in this directory.
# Each marked test/<dir>/ is built as module <dir>; success = compiles.
ROOT="$(cd .. && pwd)"
for d in */; do
  d="${d%/}"
  [ -f "$d/.multifile" ] || continue
  out=$(cd "$d" && "$ROOT/Mara.exe" build "$d" 2>&1)
  if echo "$out" | grep -q "Compiled module"; then pass=$((pass+1)); else echo "REGRESSION (multi-file subdir, want pass): $d"; bad=$((bad+1)); fi
  rm -f "$d/$d.exe" "$d"/*.ll "$d"/*.o "$d/output.ll" 2>/dev/null
done

echo "----"
echo "pass=$pass  xfail=$xfail  skip=$skip  mismatches=$bad"
[ $bad -eq 0 ] && { echo "OK — all fixtures matched expectations"; exit 0; } || exit 1
