#!/usr/bin/env bash
set -euo pipefail
project_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$project_dir"

# Keep the largest kernel certificate and linear-algebra builds separate.
lake build SerreMarkov.Matrix
lake build SerreMarkov.Intrinsic
lake build SerreMarkov.IntrinsicFrame
lake build SerreMarkov.ReflectionHurwitz
lake build SerreMarkov.RationalLattice
lake build SerreMarkov.DegenerateClassification
# The numbered census leaves do not depend on one another. Prebuild each
# before an aggregate target can schedule many kernel checks at once.
shopt -s nullglob
for source in SerreMarkov/CensusPart[0-9]*.lean SerreMarkov/Positive*Part[0-9]*.lean; do
  module=${source%.lean}
  lake build "${module//\//.}"
done
lake build SerreMarkov.ArbitraryBetaCensus
# The polynomial certificates can each take several minutes to check.
# Build the largest independent modules serially to keep memory bounded.
lake build SerreMarkov.PositiveSortedFour
lake build SerreMarkov.PositiveSortedThreeLarge
lake build SerreMarkov.PositiveSortedLargeGuards
lake build SerreMarkov.PositiveSortedLargeMinus
lake build SerreMarkov.PositiveSortedLargePlus
lake build SerreMarkov.PositiveSortedFiveLargeMinus
lake build SerreMarkov.PositiveSortedFiveLargePlus
lake build SerreMarkov.FullClassification
lake build
