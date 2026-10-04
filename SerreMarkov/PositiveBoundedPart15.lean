import SerreMarkov.PositiveBoundedPart14

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_15_00 : blockCheck 15 0 = true := by decide +kernel

theorem block_15_01 : blockCheck 15 1 = true := by decide +kernel

theorem block_15_02 : blockCheck 15 2 = true := by decide +kernel

theorem block_15_03 : blockCheck 15 3 = true := by decide +kernel

theorem block_15_04 : blockCheck 15 4 = true := by decide +kernel

theorem checked_row_15 (b : Fin 20) (h : 15+b.val ≤ 19) :
    blockCheck 15 b.val = true := by
  fin_cases b
  · exact block_15_00
  · exact block_15_01
  · exact block_15_02
  · exact block_15_03
  · exact block_15_04
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

end SerreMarkov.PositiveBounded
