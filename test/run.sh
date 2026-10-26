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
# A compiling fixture may also carry `//@ expect-output: text` lines (any
# number): it is then RUN, and must exit 0 with each text in its output. That's
# how a miscompile that still compiles — printing nothing, say — gets caught.
# A `//@ expect-exit: N` line makes N the exit it must give instead: a program
# a run-time check stops (1), its message among the expected output.
# A `//@ build-flags: flags` line builds it with those flags (`-no assert`).
# `//@ expect-warning: text` lines (any number): it must still compile, each
# text among what the build says — a warning that has to be given.
#
# The docs' programs, doc/*.mara, are checked too: each must build and run.
#
# New fixtures should use the //@ annotations; the lists are a migration shim.
# (test/failures/*.mara have no main and can't build standalone — out of scope
#  until `mara` grows a check-only mode.)

cd "$(dirname "$0")" || exit 2
# A program's file: `name.exe` on Windows, `name` elsewhere (Linux). The
# compiler: the debug build, mara_dev — or mara_dev.exe, as Windows names it.
case "$(uname -s)" in MINGW*|MSYS*|CYGWIN*) EXE=.exe ;; *) EXE= ;; esac
MARA=${MARA_EXE:-$PWD/../mara_dev$EXE}   # (MARA_EXE=… names another)
if [ -z "${MARA_EXE:-}" ] && [ ! -x "$MARA" ] && [ -x "$PWD/../mara_dev.exe" ]; then MARA=$PWD/../mara_dev.exe; fi


LEGACY_FAIL="capsize_neg clangfail erruse_neg escape_struct_lit_neg fixed_decay_neg widenneg"
# name:reason — stale/pre-existing-broken fixtures that DO have a main (so they
# won't auto-skip). Clean these up and the entries go away.
LEGACY_SKIP="leak_consumer:stale-multimodule-uses-removed-Arena_Basic"

in_list() { case " $1 " in *" $2 "*) return 0 ;; esac; return 1; }
skip_reason() { for kv in $LEGACY_SKIP; do case "$kv" in "$1:"*) echo "${kv#*:}"; return ;; esac; done; }

# The fixtures are checked in parallel (JOBS at a time, default every core):
# each writes its verdict to its own file in $RES — the first line pass,
# xfail, skip or bad, then what to say about it; they're tallied afterwards in
# fixture order.
JOBS=${JOBS:-$(nproc 2>/dev/null || echo 4)}
RES=$(mktemp -d)
ROOT="$(cd .. && pwd)"
export MARA EXE RES ROOT LEGACY_FAIL LEGACY_SKIP
verdict() { printf '%s\n' "$2" "${3-}" > "$RES/$1.res"; }                   # key kind [message]

check_file() {  # f
  local f=$1 name="${1%.mara}" exp=pass substr="" out comp run rc missing want flags
  if grep -qE '//@ expect-fail' "$f" 2>/dev/null; then
    exp=fail
    substr=$(sed -nE 's#.*//@ expect-fail:[[:space:]]*(.+)#\1#p' "$f" | head -1 | tr -d '\r')
  elif grep -qE '//@ expect-skip:' "$f" 2>/dev/null; then
    exp=skip
  elif in_list "$LEGACY_FAIL" "$name"; then
    exp=fail
  elif [ -n "$(skip_reason "$name")" ]; then
    exp=skip
  elif ! grep -qE '^[[:space:]]*main[[:space:]]*::' "$f"; then
    exp=skip
  fi
  [ "$exp" = skip ] && { verdict "$name" skip; return; }

  flags=$(sed -nE 's#.*//@ build-flags:[[:space:]]*(.+)#\1#p' "$f" | head -1 | tr -d '\r')
  out=$("$MARA" build "$name" $flags 2>&1)
  if echo "$out" | grep -qE "has no .main|no files found"; then verdict "$name" skip; return; fi
  comp=no; echo "$out" | grep -q "Compiled module" && comp=yes

  if [ "$exp" = pass ]; then
    if [ "$comp" != yes ]; then verdict "$name" bad "REGRESSION (want pass, failed): $name"; return; fi
    while IFS= read -r want; do
      echo "$out" | grep -qF -- "$want" || { verdict "$name" bad "MISSING WARNING: $name (want: \"$want\")"; return; }
    done < <(sed -nE 's#.*//@ expect-warning:[[:space:]]*(.+)#\1#p' "$f" | tr -d '\r')
    if grep -qE '//@ expect-output:' "$f"; then
      run=$(timeout 10 "./$name$EXE" 2>&1); rc=$?
      want_rc=$(sed -nE 's#.*//@ expect-exit:[[:space:]]*([0-9]+).*#\1#p' "$f" | head -1)
      missing=""
      while IFS= read -r want; do
        echo "$run" | grep -qF -- "$want" || missing="$want"
      done < <(sed -nE 's#.*//@ expect-output:[[:space:]]*(.+)#\1#p' "$f" | tr -d '\r')
      if [ $rc -ne "${want_rc:-0}" ] || [ -n "$missing" ]; then
        verdict "$name" bad "WRONG OUTPUT: $name (exit $rc${missing:+, missing: \"$missing\"})"; return
      fi
    fi
    verdict "$name" pass
  else
    if [ "$comp" = yes ]; then verdict "$name" bad "STALE NEGATIVE (want fail, compiled): $name"
    elif [ -n "$substr" ] && ! echo "$out" | grep -qF "$substr"; then verdict "$name" bad "WRONG ERROR: $name (want substring: $substr)"
    else verdict "$name" xfail; fi
  fi
}

# Multi-file module fixtures (cross-file resolution) live in opt-in subdirs
# marked with a .multifile file. The flat per-file loop above can't combine
# them, and loose multi-file modules collide on discovery in this directory.
# Each marked test/<dir>/ is built as module <dir>; success = compiles, unless
# a file in the subdir carries //@ expect-fail[: substr] (same semantics as the
# flat loop) — used for negative multi-file properties like file-private imports.
# A .shared file there too builds it as a DLL (`-shared`: its `#expose` funs).
check_dir() {  # d
  local d=$1 key="dir.$1" exp=pass substr="" out comp flags=""
  [ -f "$d/.shared" ] && flags=-shared
  if grep -rqE '//@ expect-fail' "$d" 2>/dev/null; then
    exp=fail
    substr=$(grep -rhE '//@ expect-fail:' "$d" | sed -nE 's#.*//@ expect-fail:[[:space:]]*(.+)#\1#p' | head -1 | tr -d '\r')
  fi
  out=$(cd "$d" && "$MARA" build "$d" $flags 2>&1)
  comp=no; echo "$out" | grep -q "Compiled module" && comp=yes
  if [ "$exp" = pass ]; then
    if [ "$comp" = yes ]; then verdict "$key" pass; else verdict "$key" bad "REGRESSION (multi-file subdir, want pass): $d"; fi
  else
    if [ "$comp" = yes ]; then verdict "$key" bad "STALE NEGATIVE (multi-file subdir, want fail): $d"
    elif [ -n "$substr" ] && ! echo "$out" | grep -qF "$substr"; then verdict "$key" bad "WRONG ERROR (multi-file subdir): $d (want: $substr)"
    else verdict "$key" xfail; fi
  fi
  rm -f "$d/$d$EXE" "$d/$d.dll" "$d/$d.lib" "$d"/*.ll "$d"/*.o "$d/output.ll" 2>/dev/null
}

# The docs' programs (doc/*.mara): each must build and run with no arguments
# to exit 0 — run from doc/, where they find the files they read.
check_doc() {  # f
  local f=$1 name="${1%.mara}" key="doc.${1%.mara}" out rc
  out=$(cd "$ROOT/doc" && "$MARA" build "$name" 2>&1)
  if ! echo "$out" | grep -q "Compiled module"; then
    verdict "$key" bad "DOC DOESN'T BUILD: doc/$f"
    return
  fi
  (cd "$ROOT/doc" && timeout 10 "./$name$EXE" > /dev/null 2>&1); rc=$?
  rm -rf "$ROOT/doc/$name$EXE" "$ROOT/doc/$name.pdb" "$ROOT/doc/${name}_build"
  if [ $rc -ne 0 ]; then verdict "$key" bad "DOC FAILS WHEN RUN: doc/$f (exit $rc)"; else verdict "$key" pass; fi
}
export -f in_list skip_reason verdict check_file check_dir check_doc

dirs=()
for d in */; do d="${d%/}"; [ -f "$d/.multifile" ] && dirs+=("$d"); done
docs=($(cd ../doc && ls *.mara))
{ printf 'file %s\n' *.mara; printf 'dir %s\n' "${dirs[@]}"; printf 'doc %s\n' "${docs[@]}"; } \
  | xargs -P "$JOBS" -L 1 bash -c 'check_$0 "$1"'

pass=0; xfail=0; skip=0; bad=0
for key in $(printf '%s\n' *.mara | sed 's/\.mara$//') $(printf 'dir.%s\n' "${dirs[@]}") $(printf 'doc.%s\n' "${docs[@]}" | sed 's/\.mara$//'); do
  { read -r kind; read -r msg; } < "$RES/$key.res"
  case $kind in
    pass)  pass=$((pass+1)) ;;
    xfail) xfail=$((xfail+1)) ;;
    skip)  skip=$((skip+1)) ;;
    bad)   echo "$msg"; bad=$((bad+1)) ;;
  esac
done

echo "----"
rm -rf "$RES"
echo "pass=$pass  xfail=$xfail  skip=$skip  mismatches=$bad"
[ $bad -eq 0 ] && { echo "OK — all fixtures matched expectations"; exit 0; } || exit 1
