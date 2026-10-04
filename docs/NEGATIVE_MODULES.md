# Negative and degenerate arithmetic modules

The following modules have been compiled successfully with Lean 4.24.0.
All reachability conclusions provide finite words in the defined generators.
No theorem assumes the global classification or an unproved geometric result.

## Complete degenerate classification

`SerreMarkov/DegenerateClassification.lean` now proves the entire degenerate
classification from the original six integer entries and the equations
`q1=8`, `q2²=16`, `(S+1)³=0`:

- `SerreMarkov.degenerate_classification`: a unique integer `k ≥ 0` is reached by a finite signed mutation word as `family k (-k)`.
- `SerreMarkov.degenerate_lattice_classification`: the same unique parameter classifies the integral Euler lattice.
- `SerreMarkov.degenerate_iff_reachable_family` and `degenerate_iff_latticeEquivalent_family`: both normal-form conclusions also imply the original solution and degeneracy conditions.
- `SerreMarkov.degenerate_latticeEquivalent_iff_reachable`: on all degenerate solutions, Euler-lattice isomorphism is equivalent to signed mutation equivalence.

The proof depends on the explicit adjugate algebra in
`SerreMarkov/DegenerateAlgebra.lean`, the terminating integer cubic descent
in `DegenerateReduction.lean`, and the second-minor divisor invariant in
`MinorContent.lean`. `DegenerateUniqueness.lean` separates every nonnegative
parameter, including the rank-one case `k=2`.

`SerreMarkov/SerreInvariant.lean` proves that all powers of the shifted Serre
operator transform by integral unit conjugation. In particular, vanishing
of every fixed power is invariant under arbitrary integral Euler-lattice
isomorphisms and under signed mutation words.

## Family normalization

`SerreMarkov/Normalize.lean` proves:

- `SerreMarkov.family_shift_int`: every integral multiple of the parameter sum is realized by a finite mutation word.
- `SerreMarkov.family_reduce_mod`: division reduces the second parameter modulo a positive sum.
- `SerreMarkov.family_normalize`: if `x+y ≠ 0`, there are reachable parameters `x',y'` with `x' ≥ y' ≥ 0` and `x'+y'=|x+y|`.
- `SerreMarkov.family_normalize_degenerate`: a zero-sum pair reaches `family k (-k)` with `k ≥ 0`.

## Dihedral Hurwitz reduction

`SerreMarkov/Dihedral.lean` imports only Lean core. Integer labels use the actual adjacent operations `(a,b) ↦ (2a-b,a)` and their inverses.

- `SerreMarkov.Dihedral.pairReach_lift`: elementary Euclidean operations lift to actual finite Hurwitz words, including the changing base label.
- `SerreMarkov.Dihedral.pairReach_reduce_gcd`: the Euclidean algorithm reaches `(gcd(u,v),0)`. Termination is proved by strong induction on the absolute value of the second coordinate.
- `SerreMarkov.Dihedral.identity_product_hurwitz`: an integer quadruple with alternating sum zero reaches `(a,a+g,a+g,a)` for some `g ≥ 0`.

`SerreMarkov/DihedralFinite.lean` proves `SerreMarkov.Dihedral.identity_product_hurwitz_mod`: if the alternating sum is divisible by a modulus `m`, the same conclusion holds modulo `m`, for a finite word acting on the original labels. This adjusts an integer lift and proves that all moves respect congruence.

## Full two-Kronecker slice

`SerreMarkov/KroneckerNormalize.lean` proves:

- `SerreMarkov.kroneckerPlus_shift_u` and `kroneckerPlus_shift_v`: arbitrary integral translations in either parameter.
- `SerreMarkov.kroneckerPlus_reduce_mod`: both parameters reduce modulo four while maintaining the defining equation.
- `SerreMarkov.kroneckerPlus_residue_family`: all admissible residues reduce to the family by eight kernel-checked concrete certificates.
- `SerreMarkov.kronecker_slice_reachable_family`: every six-tuple `(-2,b,c,d,e,2)` satisfying `q1=8`, `q2²=16` reaches some family member. Both positive Pfaffian components, of sums `4` and `-4`, are covered, along with the negative Pfaffian component.

## Axiom inspection

`#print axioms` for the normalization, dihedral, complete degenerate
classification, lattice uniqueness, and shifted-Serre invariance headline
theorems reports only the standard Lean axioms `propext`, `Classical.choice`,
and `Quot.sound`. No `sorryAx`, custom axiom, or `native_decide` is present.

The independently implemented `SerreMarkov/BetaNormalization.lean` and
`SerreMarkov/ArbitraryBetaCensus.lean` also pass the same axiom inspection.
They normalize an arbitrary fixed-point-free cubic permutation on twelve
vertices by cycle-type conjugacy, transport the transitivity and cusp-orbit
hypotheses, and deduce a unique simultaneous-conjugacy representative from
the fully checked finite census.

## Degenerate integral reduction

`SerreMarkov/DegenerateNormalForm.lean` defines the reduced presentation
`(a,b,-d,d,b-ad,-a)`. `SerreMarkov/DegenerateReduction.lean` proves
`SerreMarkov.reducedDegenerate_reachable_family`: every integral solution of
`a²+b²+d²-abd=4` reaches `family k (-k)` for a nonnegative integer `k`.
The proof uses genuine signed mutation words and strong induction on
`|a|+|b|+|d|`. The positive descent and small integer cases are supplied by
`SerreMarkov/MarkovDescent.lean`.

`SerreMarkov/MinorContent.lean` proves the universal double-sum multiplication
formulas for ordered second minors. Consequently, arbitrary integral Euler
lattice isomorphisms preserve divisibility of all second minors of the
symmetric form. On `family k (-k)` this invariant is precisely divisibility
of `4-k²`; thus `SerreMarkov.degenerate_family_minor_content` preserves
`|4-k²|`. All ordered minors are proved directly in Lean, including the
vanishing rank-one case `k=2`.

## Scope

These are complete formal proofs of the stated arithmetic reductions. They do
not yet prove that every negative-signature input reaches a repeated
reflection pair. That requires the intrinsic lattice construction and
chamber theory. The degenerate classification instead uses direct integral
algebra and the terminating cubic descent, avoiding a separate dihedral
lattice model. The independent mathematical audit found no fatal gap in the
manuscript's geometric arguments; see the accompanying audit report.
