import SerreMarkov.PositiveSmallEndpointCore
import SerreMarkov.PositiveSmallEndpointChecks
import SerreMarkov.PositiveBoundedCensus

/-! # Classification with two small opposite endpoints

The proved endpoint-specific caps and complete kernel census bring every
such terminal chamber point into the already classified bounded region. -/

namespace SerreMarkov.PositiveSmallEndpointCensus

open PositiveChamber PositiveShortWord PositiveBounded

theorem small_endpoints_total_bound (z : Six) (hz : Chamber z)
    (ha5 : z.a ≤ 5) (hf5 : z.f ≤ 5) (ht : ShortTerminal z 2) :
    z.a+z.b+z.c+z.d+z.e+z.f ≤ 37 :=
  checked_small_endpoints_total_bound all_blocks_checked z hz ha5 hf5 ht

theorem small_endpoints_bounded (z : Six) (hz : Chamber z)
    (ha5 : z.a ≤ 5) (hf5 : z.f ≤ 5) (ht : ShortTerminal z 2) : Bounded z := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hz.2.2
  exact ⟨hz.1,ha,hb,hc,hd,he,hf,hz.2.1,small_endpoints_total_bound z hz ha5 hf5 ht⟩

/-- Every terminal positive solution with both opposite endpoints at most
five lies in exactly one actual sporadic mutation orbit. -/
theorem small_endpoints_classification_unique (z : Six) (hz : Chamber z)
    (ha5 : z.a ≤ 5) (hf5 : z.f ≤ 5) (ht : ShortTerminal z 2) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) :=
  bounded_classification_unique z (small_endpoints_bounded z hz ha5 hf5 ht)

end SerreMarkov.PositiveSmallEndpointCensus
