# Immediate next steps

## What has already been recovered

According to the Work handoff:

- Default `lake build` passed (3460 jobs).
- Kernel audit recorded 8059 theorem declarations and 1118 definition/opaque/axiom declarations in the verified closure.
- Source scan found 0 occurrences of `sorry`, `admit`, `axiom`, `sorryAx`, `native_decide` after excluding comments/strings as described by the handoff.
- Negative classification is reported complete and default-build verified.
- Degenerate classification and Jordan-type results are reported complete and verified.
- Family normalization, isometry criterion, fiber formulas, and unboundedness are reported complete and verified.
- Modular presentation and the conditional index-12 finite classification are reported complete and verified.
- `PositiveClassificationFull.lean` and `FullClassification.lean` exist, but are outside the default build and their final extended verification was interrupted.

## Highest-priority question

Does the existing direct-algebraic positive classification actually kernel-check without bounds?

This is the only question to answer before starting new formalization.

## Recommended first Codex task

Use the exact prompt in `CODEX_FIRST_TASK.txt`.

Expected successful endpoint:

1. every large positive certificate compiles serially;
2. `SerreMarkov.PositiveClassificationFull` compiles;
3. `SerreMarkov.FullClassification` compiles;
4. the full theorem is imported into the default root;
5. `lake build` and the axiom audit pass afterward;
6. Git contains a checkpoint.

## After that

Decide which target is intended:

- **A. Formalize the mathematical results of the paper.** Then reconcile theorem statements one-by-one with the paper and complete any missing result declarations. The existing direct algebraic proof is acceptable even where it differs from the paper.
- **B. Formalize the actual proof route of the paper.** Keep the result-complete code and separately formalize the geometric route: reflection chambers, cusp primitivity, proper maps and degree, finite-area Fuchsian group arguments, and the reconstruction of the positive Gram matrix.

For a publication companion formalization, A first and B second is strongly recommended.
