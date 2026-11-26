#!/usr/bin/env bash
# Optional helper for a preinstalled Lean and cached dependencies.
# Portable builds should use `lake build`; this helper never builds dependencies.
set -euo pipefail
ut_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
ut_lean="${UNIFORM_TURAN_LEAN_BIN:-}"
if [[ -z "$ut_lean" ]]; then
  if command -v lean >/dev/null 2>&1; then
    ut_lean="$(command -v lean)"
  elif [[ -x /workspace/scratch/2f4694a9bf7a/toolchains/lean-4.35.0-rc2-linux/bin/lean ]]; then
    ut_lean=/workspace/scratch/2f4694a9bf7a/toolchains/lean-4.35.0-rc2-linux/bin/lean
  else
    echo 'Set UNIFORM_TURAN_LEAN_BIN to the pinned Lean executable.' >&2
    exit 1
  fi
fi
if [[ $# -ne 1 ]]; then
  echo 'Usage: scripts/lean-local.sh <project-relative .lean file>' >&2
  exit 2
fi
ut_input="$1"
if [[ "$ut_input" == /* ]]; then
  ut_input="${ut_input#"$ut_root"/}"
fi
if [[ "$ut_input" == /* || "$ut_input" == ../* || "$ut_input" != *.lean ]]; then
  echo 'The source file must be inside this project and end in .lean.' >&2
  exit 2
fi
ut_packages="${UNIFORM_TURAN_PACKAGE_ROOT:-$ut_root/.lake/packages}"
ut_lib="$ut_root/.lake/build/lib/lean"
ut_path="$ut_lib"
for ut_pkg in "$ut_packages"/*; do
  if [[ -d "$ut_pkg/.lake/build/lib/lean" ]]; then
    ut_path="$ut_path:$ut_pkg/.lake/build/lib/lean"
  fi
done
export LEAN_PATH="$ut_path${LEAN_PATH:+:$LEAN_PATH}"
ut_output="$ut_lib/${ut_input%.lean}"
mkdir -p -- "$(dirname -- "$ut_output")"
cd -- "$ut_root"
exec "$ut_lean" -j "${UNIFORM_TURAN_THREADS:-2}" -R "$ut_root" -o "$ut_output.olean" -i "$ut_output.ilean" "$ut_input"
