# Serre–Markov v4: Lean formalization

Lean 4.24.0 / mathlib v4.24.0. The project formalizes the integer algebra of the manuscript and several classification and fiber results. The negative and degenerate classifications, and exact full negative fibers, are formalized without classification hypotheses. The general positive classification remains unfinished. `STATUS_ja.md` gives the exact boundary; `PLAN_ja.md` records the full target and dependencies.

## Reproduce

With Elan installed, unpack this source archive and run:

```sh
lake exe cache get
./scripts/verify.sh
```

`verify.sh` checks the largest modules in sequence to control peak memory, then builds the entire project and its default axiom-audit target. A subsequent `lake build` is also sufficient.

Keep `lean-toolchain` and `lake-manifest.json`; they pin the versions used for validation. `scripts/generate_census.py` reproduces finite certificates, but Python is not trusted by the proofs: Lean checks the certificates and proves enumeration completeness.

The code uses no `sorry`, extra mathematical axioms, or `native_decide`. The audit traverses the compiled theorems, definitions and their dependencies, rejecting every axiom except `propext`, `Classical.choice`, and `Quot.sound`.

## Main verified results

- `NegativeClassificationFull.negative_classification`: every negative integer solution has exactly one normalized family representative, by exhaustive genuine reductions and unrestricted-word strong induction.
- `NegativeClassificationFull.negative_classification_with_invariants`: the unique representative identifies `A=-1` and `κ=x+y` in every primitive integral frame.
- `NegativeFamilyOrbitFibers.odd_solution_forgetful_fiber_card`: the complete actual negative fiber has the exact odd-modulus prime-factor product count.
- `NegativeFamilyOrbitFibers.fullFiber_finite`: every positive total, including even totals, has a finite full negative fiber.
- `NegativeFamilyOrbitFibers.primePower_zero_solution_forgetful_fiber_card`: the full odd prime square-power fiber has exact cardinality `(p^e+1)/2`.

- `solution_iff_fourth_power_zero`: the two integer equations are equivalent to nilpotence of the shifted Serre operator.
- `reachable_integral_congruence`: actual finite mutation and sign words produce integral basis changes.
- `basisWord_reflection_hurwitz`: actual basis mutations agree with reflection Hurwitz operations for every finite word.
- `family_normalize`, `kronecker_slice_reachable_family`: full integer family normalization and the two-Kronecker slice reduction.
- `ReflectionGroup.reachable_reflectionGroup_isometric_conjugate`: actual generated reflection subgroups are integrally isometric-conjugate along every mutation word.
- `FamilyUniqueness.normalized_positive_totals_reachable_iff`: complete normalized family mutation uniqueness for every positive total, including composite and even totals, by an algebraic reflection-word proof.
- `RootProductFormula.squareRoots_card_odd_formula`: the full prime-power/CRT square-root formula for every positive odd modulus and integer parameter.
- `FamilyOrbitFibers.odd_familyPart_card`: exact counts of the actual family-derived mutation orbits inside the full solution forgetful fiber.
- `FamilyOrbitFibers.odd_solution_forgetful_fiber_injection`: an injection of the exact family count into the full fiber, without assuming classification.
- `FamilyFiberFinite.odd_lattice_candidate_count`: the exact square-root/sign count within the normalized family.
- `FamilyFiberFinite.primePower_zero_lattice_candidate_card`: exact `(p^e+1)/2` family-candidate counts for odd prime square powers.
- `family_positive_isometry_iff`: complete integral-isometry criterion within the family, including the even-modulus case.
- `degenerate_classification`: complete degenerate classification with a unique nonnegative parameter.
- `DegenerateFibers.degenerate_fiber_card`: every actual full solution-orbit fiber over a degenerate solution lattice has cardinality one.
- `IntrinsicUnique.solution_regular_unique_parameters`: the intrinsic `(A,κ)` is independent of every flag and frame choice, and is preserved by every integral Euler isometry.
- `IntrinsicSignature.real_frame_diagonal_congruence`: an explicit real unit congruence to `diag(2,-2,-2A,0)`.
- `IntrinsicFrame.solution_regular_has_frame`: an integral adapted frame for every regular solution; its cube tensor, content formula and universal Riemann–Roch identity are verified.
- `NegativeAdjacentReduction.negative_reachable_first_edge_cases`: unconditional reduction of every negative solution to first edge 0, 1, or 2, via actual mutation words and well-founded large-edge descent.
- `PositiveBounded.positive_solution_bounded_classification`: every actual positive solution of L1 height at most 37 belongs to exactly one of the five representative mutation orbits.
- `ModularPingPong.presentationPSLEquiv`: the actual modular-group presentation, proved by integer Euclid and free-product ping-pong.
- `ModularPSLCensus.subgroup_census_unique`: classification of actual PSL2(Z) subgroups under the explicit index and coset conditions.
- `NegativeAtLeastTwoReduction.negative_atLeastTwo_reduction`: unconditional actual family reachability or strict original-height descent when all six absolute values are at least two.
- `NegativeTinyReduction.negative_reachable_tiny_or_family`: strong-induction termination at the family or at a zero/unit edge.
- `NegativeZeroOffdiagonal.offdiagonal_zero_family_or_drop`: complete zero-edge reduction in four coordinate positions, with all other coefficients arbitrary.
- `PositiveSmallEndpointCensus.small_endpoints_classification_unique`: all nine small-opposite-edge terminal slices belong to exactly one original sporadic orbit, with complete kernel finite coverage.
- `PositiveSortedTerminal.positive_solution_sorted_terminal_reduction`: unrestricted positive classification reduces to ordered globally terminal chambers, preserving each actual representative orbit membership.
- `NegativeLatticeCriterion.negative_orbit_and_lattice_criteria`: exact mutation and integral lattice criteria for any two negative solutions after constructing their normalized representatives.
- `PositiveEndpointBounds.small_endpoints_sum_bound`: endpoint pairs in three through five have explicit finite remaining-coordinate bounds from actual one-letter guards and a universal polynomial identity.
- `PositiveSmallThreeTerminal`, `PositiveFourFourChecks`, `PositiveFourFiveChecks`, `PositiveFiveFiveCensus`: complete actual-orbit classifications of proved finite small-adjacent-edge terminal slices, without an assumed initial height bound.
- `NegativeFiberFiniteGeneral.negative_solution_fiber_finite`: the full fiber over the lattice of any negative solution is finite.
- `PositiveTriangleLower.chamber_all_triangle_bounds`: all four triangle defects are at most minus seven in every positive integer chamber, without a no-drop assumption.
- `CanonicalRepresentatives.representatives_reachable_iff`: joint unconditional uniqueness of the three kinds of canonical representatives in the actual solution orbit quotient.
- `IndexTwelve.arbitrary_beta_census_unique`: complete finite simultaneous permutation classification for arbitrary admissible alpha and beta.
- `RationalClifford.normalized_even_words_integral_SL2_positive_conjugation`: a common positive rational conjugation into integral SL2 for all even words from the stated Clifford data.
- `Fibers.regular_integral_isometry_distinct_mutation_orbits`: the explicit rank-four lattice counterexample.
- `Unbounded.unbounded_isometry_fibers`: for every `n`, an actual rank-four integral Euler lattice with `n+1` distinct signed mutation orbits.
- `unbounded_solutionForgetfulMap_fibers`: the same unboundedness on the actual quotient forgetful map.

See `STATUS_ja.md` for additional verified modules and remaining obligations. Representative checks and finite permutation classification are distinguished from the geometric reduction of arbitrary solutions.

The older `NegativeClassification` and `ConditionalFamilyOrbitFibers` APIs retain an explicit short-word hypothesis. The completed `NegativeClassificationFull` and `NegativeFamilyOrbitFibers` APIs remove that hypothesis through separate, fully proved unrestricted-word reductions. No unproved classification statement is used as an axiom.

`tooling/ENVIRONMENT.md` documents the optional execution-environment shim used in Work Mode. It changes executable discovery only and is unnecessary on an ordinary machine. No compiler binaries or dependency caches are included in the archive.
