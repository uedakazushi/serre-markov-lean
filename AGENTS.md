# SerreMarkov Lean — Codex instructions

## Mission

Recover and complete the existing Lean 4.24.0 / mathlib v4.24.0 formalization of the rank-four Serre–Markov classification. Do not restart the project from scratch.

The recovered project already has a successful default `lake build`, no `sorry` / `admit` / explicit project `axiom`, and substantial completed mathematics. The immediate objective is to verify the source modules outside the default build, especially the unrestricted positive classification, and then promote the full classification into the default build.

## Source of truth

- Lean sources and pinned dependencies in this repository.
- `HANDOFF.md`, `STATUS.md`, `GAPS.md`, `PAPER_MAP.md` describe the recovered state.
- Do not treat old build logs as current proof certificates; rerun the relevant build.
- Do not weaken theorem statements to make compilation succeed.

## Global proof policy

1. Keep `lake build` passing at every checkpoint.
2. Do not introduce `sorry`, `admit`, new project axioms, or opaque assumptions standing in for mathematical content.
3. Allowed foundational axioms in audit output are only the ordinary Lean/mathlib ones already recorded: `propext`, `Classical.choice`, `Quot.sound`.
4. Never replace a theorem by a stronger hypothesis merely to complete the pipeline.
5. If a theorem or generated polynomial certificate is false, record an exact counterexample in `GAPS.md` and preserve the failing source.
6. Generated finite certificates may be used when their exhaustive coverage is proved or checked in Lean. A bounded experiment is not a proof of an unbounded theorem.
7. Large certificate modules must be compiled serially; avoid parallel builds that cause memory pressure.
8. After every substantial milestone, update `STATUS.md` and create a Git commit.

## First task: verification only

Before doing new mathematics:

1. Confirm `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json` are unchanged and pinned to Lean/mathlib 4.24.0.
2. Run `lake exe cache get` if needed.
3. Run `lake build`; this is expected to pass.
4. Search project source for `sorry`, `admit`, `axiom`, `sorryAx`; record the result.
5. Build the large modules outside the default build serially, using `scripts/verify.sh` as the intended order. Do not modify proof source merely because a large module is slow.
6. In particular obtain explicit pass/fail results for:
   - `SerreMarkov.PositiveSortedLargeGuards`
   - `SerreMarkov.PositiveSortedLargeMinus`
   - `SerreMarkov.PositiveSortedLargePlus`
   - `SerreMarkov.PositiveSortedFiveLargeMinus`
   - `SerreMarkov.PositiveSortedFiveLargePlus`
   - `SerreMarkov.PositiveSortedFiveLarge`
   - `SerreMarkov.PositiveSortedLarge`
   - `SerreMarkov.PositiveClassificationFull`
   - `SerreMarkov.FullClassification`
7. Create `RECOVERY_AUDIT.md` with timings, peak-memory observations if available, exact errors if any, and the theorem names successfully checked.
8. Do not begin new geometric formalization until this audit is complete.

## Milestone F0: promote full classification

If `SerreMarkov.FullClassification` compiles:

1. Audit its declarations for unwanted axioms.
2. Import `SerreMarkov.FullClassification` from the default root `SerreMarkov.lean` (or otherwise add it to the default library target without circular imports).
3. Run full `lake build` again.
4. Run the declaration/axiom audit again.
5. Update `PAPER_MAP.md` and `STATUS.md` so that the paper's full classification theorem and global fiber finiteness are marked as kernel-checked only if the corresponding declarations are actually in the verified import closure.
6. Commit this as a dedicated milestone.

## Milestone F1: repair full classification if needed

If the outside-default modules fail:

- Work from the earliest failing dependency upward.
- Prefer fixing proof engineering / resource issues without changing theorem statements.
- If a generated certificate is the bottleneck, verify its generator and coverage before regenerating it.
- Split independent certificates into smaller modules if necessary, but retain a theorem proving their exhaustive aggregation.
- Record every source-level change and why it is logically conservative.

## Two notions of completion

Keep these explicitly distinct in `STATUS.md`:

### Result-complete
The exact mathematical theorem statements of the paper (classification, uniqueness, fiber formula, decidability where claimed) are kernel-checked, perhaps by a Lean proof different from the paper's geometric proof.

### Proof-route-complete
The principal proof route written in the paper is itself formalized: hyperbolic reflection chambers, cusp primitivity, proper-map/peripheral degree, finite-covolume Fuchsian groups, elliptic involution reconstruction, and the geometric Hurwitz bridge.

The recovered code appears close to **result-complete** by a direct algebraic positive-classification route, but is not yet **proof-route-complete**. Never conflate these.

## After F0/F1

Only after the result-complete classification is in the default verified build:

1. Produce `FORMALIZATION_AUDIT.md` mapping every theorem/lemma in `PAPER_MAP.md` to Lean declarations and files.
2. Mark whether each item is:
   - exact proof-route formalization,
   - alternative proof of the same theorem,
   - finite computational certificate,
   - not yet formalized.
3. Then plan the geometric API gaps separately. Do not risk the already completed algebraic classification while formalizing geometry.

## Git discipline

This recovered project had no Git history. On first use, initialize Git and make an immutable baseline commit before editing source. Suggested first commits:

- `recovery: import Work checkpoint`
- `audit: verify default build`
- `audit: verify full classification modules`
- `milestone: promote full classification to default build`

Do not commit `.lake` build caches or external compiler distributions.
