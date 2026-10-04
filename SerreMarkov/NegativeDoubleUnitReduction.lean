import SerreMarkov.BoundaryPatterns
import SerreMarkov.NegativeAdjacentUnits
import SerreMarkov.NegativeDiagonalAdjacentUnits
import SerreMarkov.NegativeEndpointUnits
import SerreMarkov.NegativeCrossingUnits

/-! # Complete reduction at any two unit coordinates

The four pair patterns exhaust all fifteen unordered pairs of coordinates.
Each branch supplies an actual family reachability witness or a mutation word
whose full six-coordinate height is strictly smaller than the original height.
-/

namespace SerreMarkov.NegativeDoubleUnitReduction
open NegativeTwoEdge BoundaryPatterns

theorem double_unit_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (hu : DoubleUnit z) :
    FamilyOrDrop z := by
  rcases hu with hadj | hdiag | hopp | hcross
  · exact NegativeAdjacentUnits.neighboring_unit_edges_family_or_drop z hz hneg hadj
  · exact NegativeDiagonalAdjacentUnits.diagonal_adjacent_units_family_or_drop
      z hz hneg hdiag.1 hdiag.2
  · rcases hopp with ⟨ha,hf⟩ | ⟨hc,hd⟩
    · exact NegativeEndpointUnits.signed_endpoint_units_family_or_drop z hz hneg ha hf
    · apply CyclicMutation.family_or_drop_transfer z 1
      exact NegativeEndpointUnits.signed_endpoint_units_family_or_drop _
        (CyclicMutation.cyclePower_solution z hz 1)
        (CyclicMutation.cyclePower_negative z hneg 1)
        (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hd)
        (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hc)
  · exact NegativeCrossingUnits.signed_crossing_units_family_or_drop z hz hcross.1 hcross.2

end SerreMarkov.NegativeDoubleUnitReduction
