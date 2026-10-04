#!/usr/bin/env python3
"""Split kernel reduction of census coverage into 11 bounded-memory blocks."""
from pathlib import Path

root = Path(__file__).resolve().parents[1] / "SerreMarkov"
for j in range(11):
    previous = "CensusCoverageBase" if j == 0 else f"CensusCoverage{j-1:02d}"
    source = f'''import SerreMarkov.{previous}

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000

namespace SerreMarkov.IndexTwelve

theorem censusPartnerBlock{j:02d}_projection :
    (censusPartnerBlock {j}).map (fun row => vertexCode row.alpha) =
      matchingPartnerBlock {j} := by
  apply (List.map_injective_iff.mpr encodeMap_injective)
  decide +kernel

end SerreMarkov.IndexTwelve
'''
    (root / f"CensusCoverage{j:02d}.lean").write_text(source)
