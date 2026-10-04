import SerreMarkov.CensusCoverage07

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000

namespace SerreMarkov.IndexTwelve

theorem censusPartnerBlock08_projection :
    (censusPartnerBlock 8).map (fun row => vertexCode row.alpha) =
      matchingPartnerBlock 8 := by
  apply (List.map_injective_iff.mpr encodeMap_injective)
  decide +kernel

end SerreMarkov.IndexTwelve
