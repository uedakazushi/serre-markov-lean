# Reproducible environment

Pinned versions:

- Lean 4.24.0 (release commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`)
- mathlib v4.24.0 (commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`)

On an ordinary machine with Elan:

```sh
lake exe cache get
./scripts/verify.sh
```

The code itself does not require the environment workaround below.

## Work Mode execution environment

The sandbox has a PID namespace whose numbers do not match the mounted `/proc` tree. Lean 4.24.0's C++ executable path lookup reads `/proc/<getpid()>/exe`, which therefore fails. `tooling/proc_self.c` interposes `readlink` and substitutes `/proc/self/exe` for numeric executable paths. This changes only runtime executable discovery, not Lean elaboration or kernel checking.

For the current workspace:

```sh
export SERRE_MARKOV_LEAN_ROOT=/workspace/scratch/41606fe60bc9/lean-runtime-test/lean-4.24.0-linux
export SERRE_MARKOV_PROC_SELF_FIX=1
./tooling/with_lean.sh ./scripts/verify.sh
```

The shim is compiled into `.lake/proc_self.so` on first use. It is unnecessary in ordinary environments and is disabled by default.

The downloaded Linux compiler archive was verified locally with SHA-256
`b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec`.

The wrapper also sets `LD_LIBRARY_PATH` to the compiler library directory and, when the sandbox fix is enabled, sets `TAR_OPTIONS=--no-same-owner` because uid changes are unavailable in the user namespace.

The downloaded compiler and cached dependency build directories are not part of the source deliverable.
