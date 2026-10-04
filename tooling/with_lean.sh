#!/usr/bin/env bash
set -euo pipefail
project_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
if [ -n "${SERRE_MARKOV_LEAN_ROOT:-}" ]; then
  export PATH="$SERRE_MARKOV_LEAN_ROOT/bin:$PATH"
  export LD_LIBRARY_PATH="$SERRE_MARKOV_LEAN_ROOT/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
fi
if [ "${SERRE_MARKOV_PROC_SELF_FIX:-0}" = 1 ]; then
  shim="$project_dir/.lake/proc_self.so"
  if [ ! -f "$shim" ]; then
    mkdir -p "$project_dir/.lake"
    cc -shared -fPIC -o "$shim" "$project_dir/tooling/proc_self.c" -ldl
  fi
  export LD_PRELOAD="$shim${LD_PRELOAD:+:$LD_PRELOAD}"
  export TAR_OPTIONS="--no-same-owner${TAR_OPTIONS:+ $TAR_OPTIONS}"
fi
exec "$@"
