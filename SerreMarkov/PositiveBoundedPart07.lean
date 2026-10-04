import SerreMarkov.PositiveBoundedPart06

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_07_00 : blockCheck 7 0 = true := by decide +kernel

theorem block_07_01 : blockCheck 7 1 = true := by decide +kernel

theorem block_07_02 : blockCheck 7 2 = true := by decide +kernel

theorem block_07_03 : blockCheck 7 3 = true := by decide +kernel

theorem block_07_04 : blockCheck 7 4 = true := by decide +kernel

theorem block_07_05 : blockCheck 7 5 = true := by decide +kernel

theorem block_07_06 : blockCheck 7 6 = true := by decide +kernel

theorem block_07_07 : blockCheck 7 7 = true := by decide +kernel

theorem block_07_08 : blockCheck 7 8 = true := by decide +kernel

theorem block_07_09 : blockCheck 7 9 = true := by decide +kernel

theorem block_07_10 : blockCheck 7 10 = true := by decide +kernel

theorem block_07_11 : blockCheck 7 11 = true := by decide +kernel

theorem block_07_12 : blockCheck 7 12 = true := by decide +kernel

theorem checked_row_07 (b : Fin 20) (h : 7+b.val ≤ 19) :
    blockCheck 7 b.val = true := by
  fin_cases b
  · exact block_07_00
  · exact block_07_01
  · exact block_07_02
  · exact block_07_03
  · exact block_07_04
  · exact block_07_05
  · exact block_07_06
  · exact block_07_07
  · exact block_07_08
  · exact block_07_09
  · exact block_07_10
  · exact block_07_11
  · exact block_07_12
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

end SerreMarkov.PositiveBounded
