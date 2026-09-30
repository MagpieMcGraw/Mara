#!/usr/bin/env bash
# Mara.exe with the new checker (design/flat_tree.md, stage 3): tcdiff.sh's
# second side.
MARA_CHECKER=new exec "$(cd "$(dirname "$0")/.." && pwd)/Mara.exe" "$@"
