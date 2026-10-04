import SerreMarkov.PositiveSmallEndpointPart00
import SerreMarkov.PositiveSmallEndpointPart01
import SerreMarkov.PositiveSmallEndpointPart02
import SerreMarkov.PositiveSmallEndpointPart03
import SerreMarkov.PositiveSmallEndpointPart04
import SerreMarkov.PositiveSmallEndpointPart05
import SerreMarkov.PositiveSmallEndpointPart06
import SerreMarkov.PositiveSmallEndpointPart07
import SerreMarkov.PositiveSmallEndpointPart08

namespace SerreMarkov.PositiveSmallEndpointCensus

theorem all_blocks_checked (a f : Fin 3) (b : Fin 52) : blockCheck a.val f.val b.val=true := by
  fin_cases a <;> fin_cases f
  · exact checked_0_0 b
  · exact checked_0_1 b
  · exact checked_0_2 b
  · exact checked_1_0 b
  · exact checked_1_1 b
  · exact checked_1_2 b
  · exact checked_2_0 b
  · exact checked_2_1 b
  · exact checked_2_2 b

end SerreMarkov.PositiveSmallEndpointCensus
