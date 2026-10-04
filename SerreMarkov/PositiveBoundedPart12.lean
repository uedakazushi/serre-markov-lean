import SerreMarkov.PositiveBoundedPart11

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_12_00 : blockCheck 12 0 = true := by decide +kernel

theorem block_12_01 : blockCheck 12 1 = true := by decide +kernel

theorem block_12_02 : blockCheck 12 2 = true := by decide +kernel

theorem block_12_03 : blockCheck 12 3 = true := by decide +kernel

theorem block_12_04 : blockCheck 12 4 = true := by decide +kernel

theorem block_12_05 : blockCheck 12 5 = true := by decide +kernel

theorem block_12_06 : blockCheck 12 6 = true := by decide +kernel

theorem block_12_07 : blockCheck 12 7 = true := by decide +kernel

theorem checked_row_12 (b : Fin 20) (h : 12+b.val ≤ 19) :
    blockCheck 12 b.val = true := by
  fin_cases b
  · exact block_12_00
  · exact block_12_01
  · exact block_12_02
  · exact block_12_03
  · exact block_12_04
  · exact block_12_05
  · exact block_12_06
  · exact block_12_07
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
