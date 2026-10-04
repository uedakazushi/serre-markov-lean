import SerreMarkov.PositiveBoundedPart12

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_13_00 : blockCheck 13 0 = true := by decide +kernel

theorem block_13_01 : blockCheck 13 1 = true := by decide +kernel

theorem block_13_02 : blockCheck 13 2 = true := by decide +kernel

theorem block_13_03 : blockCheck 13 3 = true := by decide +kernel

theorem block_13_04 : blockCheck 13 4 = true := by decide +kernel

theorem block_13_05 : blockCheck 13 5 = true := by decide +kernel

theorem block_13_06 : blockCheck 13 6 = true := by decide +kernel

theorem checked_row_13 (b : Fin 20) (h : 13+b.val ≤ 19) :
    blockCheck 13 b.val = true := by
  fin_cases b
  · exact block_13_00
  · exact block_13_01
  · exact block_13_02
  · exact block_13_03
  · exact block_13_04
  · exact block_13_05
  · exact block_13_06
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
