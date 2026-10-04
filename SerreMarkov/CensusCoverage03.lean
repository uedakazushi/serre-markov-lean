import SerreMarkov.CensusCoverage02

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000

namespace SerreMarkov.IndexTwelve

theorem censusPartnerBlock03_projection :
    (censusPartnerBlock 3).map (fun row => vertexCode row.alpha) =
      matchingPartnerBlock 3 := by
  apply (List.map_injective_iff.mpr encodeMap_injective)
  decide +kernel

end SerreMarkov.IndexTwelve
