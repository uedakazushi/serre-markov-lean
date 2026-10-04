# Serre–Markov classification: Lean formalization and Blueprint

Lean 4.24.0 / mathlib v4.24.0. This project formalizes the manuscript's main classification of integer solutions under actual mutation and sign words, the forgetful-map fiber results, and terminating tests for mutation equivalence and integral Euler-lattice equivalence. The final assembly supplies the positive classification without a reduction hypothesis, completing all three kinds of canonical representatives.

The scope is these classification, fiber, and decision results. It does not include every lemma of the manuscript, its original hyperbolic-geometric proof, or its dg appendix. `STATUS_ja.md` records the exact theorem coverage; `PLAN_ja.md` records the proof route and remaining manuscript material.

The Japanese [Lean Blueprint](blueprint/README.md) explains the definitions, proof steps, mathematical dependencies and manuscript correspondence. It includes a LuaLaTeX PDF, standard Blueprint HTML with a dependency graph, compiler-derived links into the included Lean sources, and a separate declaration/axiom audit.

[Blueprint website](https://uedakazushi.github.io/serre-markov-lean/) · [Source repository](https://github.com/uedakazushi/serre-markov-lean)

The website link becomes available after the first successful Pages deployment.

## Publication

[Publication guide (Japanese)](PUBLICATION_ja.md). The included GitHub Actions workflow verifies Lean and rebuilds the Blueprint before deploying Pages from the same commit. GitHub CI has not yet been run for this preparation. Original code is MIT licensed; original explanatory prose is CC BY 4.0. See [license scope](LICENSE) and [citation metadata](CITATION.cff).

## Reproduce

With Elan installed, unpack the source archive, enter the project directory, and run:

```sh
lake exe cache get
./scripts/verify.sh
```

`verify.sh` builds the large linear-algebra modules, numbered finite-census leaves, and polynomial-certificate modules in sequence to control peak memory. It then builds `FullClassification`, the entire project, and the default `AxiomAudit` target. A subsequent `lake build` also checks the default targets. Run `lake env lean scripts/decision_examples.lean` for small executable examples of the final classification and both equivalence tests.

Keep `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json`. They pin Lean 4.24.0 (release commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`), mathlib v4.24.0 (commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`), and its dependency revisions. Compiler binaries and dependency caches are not included.

Python is unnecessary for checking the supplied Lean sources. Optional certificate regeneration uses the scripts and certificate JSON files in `scripts/`, run from the project directory, with Python 3.9 or newer and SymPy 1.14.0. The finite-census generators and `generate_positive_sorted_{four,three_large,large,five_large}.py` produce proof inputs; Python is outside the trust boundary. Lean checks the resulting finite computations, enumeration completeness, polynomial identities, and nonnegativity proofs.

The code uses no `sorry`, extra mathematical axioms, or `native_decide`. `AxiomAudit` traverses the compiled project theorems, definitions, and their transitive dependencies, rejecting every axiom except `propext`, `Classical.choice`, and `Quot.sound`. The archived verification log records the successful whole-project build and this audit.

## Main classification and decisions

All names below are in namespace `SerreMarkov`.

- `FullClassification.full_classification`: every integer solution reaches exactly one canonical representative. The list consists of the degenerate family `F(k,-k)` with `k ≥ 0`, the negative family `F(x,y)` with `0 ≤ y ≤ x` and `x+y > 0`, and the five positive representatives.
- `FullClassification.canonical_orbit_map_bijective`: these representatives give a bijection with the actual signed-mutation orbit quotient.
- `PositiveClassificationFull.positive_classification`: every positive solution belongs to exactly one of the five actual representative orbits, with no initial coefficient, height, or reduction hypothesis.
- `PositiveClassificationFull.positive_reaches_bounded`: every positive solution reaches the proved bounded region by an actual finite word.
- `NegativeClassificationFull.negative_classification` and `degenerate_classification`: unconditional existence and uniqueness in the negative and degenerate cases.
- `FullClassification.classify` and `classify_word`: a terminating search returns the canonical representative together with an actual word reaching it.
- `FullClassification.mutationEquivalentTest_correct` and `latticeEquivalentTest_correct`: computable Boolean tests decide actual mutation equivalence and integral Euler-lattice equivalence. Their inputs have type `Solution`, which includes a proof of the integer equations. No efficiency bound is claimed.
- `FullClassification.equivalenceWord_sound` and `equivalenceWord_isSome_iff`: the equivalence procedure returns an actual connecting word exactly when two solutions are mutation equivalent.

The positive proof uses sign normalization, an actual minimum-height orbit point, sorting that preserves membership in each representative orbit, universal polynomial certificates excluding the remaining ordered regions, and complete finite terminal-slice classifications. The certificates establish identities and inequalities for arbitrary coefficients; the proof does not assume that an unbounded region has been covered by finite sampling.

## Forgetful-map fibers

- `FullClassification.all_forgetful_fibers_finite`: every fiber of the actual map from solution mutation orbits to integral Euler-lattice classes is finite, including empty fibers over classes not represented by solutions.
- `FullClassification.positive_fiber_card` and `DegenerateFibers.degenerate_fiber_card`: fibers over positive and degenerate solution lattices have cardinality one.
- `NegativeFamilyOrbitFibers.fullFiberEquivCandidate` and `fullFiber_card`: each full negative fiber is exactly parameterized by a finite set of normalized congruence candidates, including even totals.
- `NegativeFamilyOrbitFibers.odd_solution_forgetful_fiber_card`: for every positive odd total, the full negative fiber has the prime-factor product count obtained from local square-root counts, CRT, and the sign quotient.
- `FullClassification.prime_square_power_fiber_card` and `prime_square_power_unique_representative`: for odd prime `p`, the fiber over `F(p^(2e),0)` has exactly `(p^e+1)/2` explicitly listed mutation-orbit representatives.
- `FullClassification.finite_fibers_and_unbounded`: every individual fiber is finite, while fiber sizes have no common bound.

The odd-modulus product formula and the finite candidate description for all positive totals are separate statements; a single odd-prime formula is not asserted for even moduli.

## Further formalized ingredients and scope

The project also includes the equivalence of the integer equations with fourth-power nilpotence of the shifted Serre operator, integral basis changes for every actual mutation word, intrinsic primitive flags and choice-independent parameters `(A,κ)`, the cube-content and Riemann–Roch identities, reflection-word proofs of general family uniqueness, and exact family lattice criteria.

The rational Clifford construction puts all even words of the stated positive half-turn data into a common conjugate of `SL₂(ℤ)`. `ModularPingPong.presentationPSLEquiv` proves the actual modular-group presentation. `ModularPSLCensus.subgroup_census_unique` classifies actual subgroups under its explicit index and coset conditions. These results do not claim that the manuscript's geometric index-12 reduction for every positive solution has been formalized.

The remaining properness, degree, signed-area, fundamental-domain, elliptic-extension, and Coxeter/Hurwitz geometric lemmas are documented in `docs/REGULAR_OBLIGATIONS_ja.md` and `POSITIVE_GEOMETRY_API_ja.md`. They belong to the original proof route and are not hypotheses of `FullClassification`. The dg appendix is outside the completed scope.

Older helper APIs such as `NegativeClassification`, `ConditionalFamilyOrbitFibers`, `FullClassificationPipeline`, and `ClassificationDecision` retain explicit completion hypotheses where documented. `NegativeClassificationFull`, `NegativeFamilyOrbitFibers`, and `FullClassification` supply the necessary proofs; the final results have no unproved classification assumption.

`tooling/ENVIRONMENT.md` documents an optional executable-discovery shim used in Work Mode. It is disabled by default and unnecessary on an ordinary machine; it does not alter Lean elaboration or kernel checking.
