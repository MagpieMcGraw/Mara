#!/usr/bin/env bash
# Fills release/: the compiler other projects build with (sooblivion copies
# it into its own compiler/ with its update_compiler.bat). Made from HEAD,
# and only when the working tree is clean and the full suite passes with
# the very Mara.exe and stdlib being released: a whole compiler home —
# Mara.exe, code/, runtime/, tools/ — and MARA_VERSION.txt saying which Mara
# it is. release/ is gitignored. Built in release.new/, swapped in when it
# passes; on a failure release/ stays as it was.
#
#   bash release.sh
set -euo pipefail
cd "$(dirname "$0")"
ROOT=$PWD

# What's released is exactly a commit.
if [ -n "$(git status --porcelain)" ]; then
  echo "release: the working tree isn't clean; commit first:"
  git status --short
  exit 1
fi
COMMIT=$(git rev-parse HEAD)
SHORT=$(git rev-parse --short=8 HEAD)
SUBJECT=$(git log -1 --format=%s)
WHEN=$(git log -1 --format=%cd --date=format:'%Y-%m-%d %H:%M')

STAGE=$ROOT/release.new
rm -rf "$STAGE"
mkdir -p "$STAGE/tools"

# The stdlib and the runtime as committed (no caches built from older ones).
git archive HEAD code runtime | tar -x -C "$STAGE"
# The toolchain: the last release's files kept where they're the same
# (a fresh clang.exe each time wakes the virus scan), copied where not.
for f in tools/*; do
  name=$(basename "$f")
  if [ -f "release/tools/$name" ] && cmp -s "$f" "release/tools/$name"; then
    cp -p "release/tools/$name" "$STAGE/tools/$name"
  else
    cp -p "$f" "$STAGE/tools/$name"
  fi
done

echo "release: building Mara.exe from $SHORT"
odin build . -o:speed -out:"$STAGE/Mara.exe" 2>&1 | grep -v 'deprecated' || true
if [ ! -f "$STAGE/Mara.exe" ]; then
  echo "release: the build failed; release/ unchanged"
  exit 1
fi

echo "release: running the suite with it"
SUITE=$(cd test && MARA_EXE="$STAGE/Mara.exe" bash run.sh 2>&1) || true
SUMMARY=$(echo "$SUITE" | grep -E '^pass=' | tail -1)
if ! echo "$SUITE" | grep -q 'OK — all fixtures matched expectations'; then
  echo "$SUITE" | tail -30
  echo "release: the suite failed; release/ unchanged"
  exit 1
fi

cat > "$STAGE/MARA_VERSION.txt" <<EOF
Mara $SHORT ($WHEN): $SUBJECT
commit $COMMIT
released $(date '+%Y-%m-%d %H:%M') by release.sh: Mara.exe built -o:speed from a clean tree
suite with this Mara.exe and stdlib: $SUMMARY
EOF

# The swap: the old release out of the way first (Windows won't move a
# folder whose Mara.exe is running: then nothing changes).
rm -rf "$ROOT/release.old"
if [ -d "$ROOT/release" ]; then
  if ! mv "$ROOT/release" "$ROOT/release.old"; then
    echo "release: release/ is in use (its Mara.exe running?); the new one is in release.new/"
    exit 1
  fi
fi
mv "$STAGE" "$ROOT/release"
rm -rf "$ROOT/release.old"
cat "$ROOT/release/MARA_VERSION.txt"
