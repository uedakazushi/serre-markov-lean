import SerreMarkov.PositiveBoundedPart04

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_05_00 : blockCheck 5 0 = true := by decide +kernel

theorem block_05_01 : blockCheck 5 1 = true := by decide +kernel

theorem block_05_02 : blockCheck 5 2 = true := by decide +kernel

theorem block_05_03 : blockCheck 5 3 = true := by decide +kernel

theorem block_05_04 : blockCheck 5 4 = true := by decide +kernel

theorem block_05_05 : blockCheck 5 5 = true := by decide +kernel

theorem block_05_06 : blockCheck 5 6 = true := by decide +kernel

theorem block_05_07 : blockCheck 5 7 = true := by decide +kernel

theorem block_05_08 : blockCheck 5 8 = true := by decide +kernel

theorem block_05_09 : blockCheck 5 9 = true := by decide +kernel

theorem block_05_10 : blockCheck 5 10 = true := by decide +kernel

theorem block_05_11 : blockCheck 5 11 = true := by decide +kernel

theorem block_05_12 : blockCheck 5 12 = true := by decide +kernel

theorem block_05_13 : blockCheck 5 13 = true := by decide +kernel

theorem block_05_14 : blockCheck 5 14 = true := by decide +kernel

theorem checked_row_05 (b : Fin 20) (h : 5+b.val ≤ 19) :
    blockCheck 5 b.val = true := by
  fin_cases b
  · exact block_05_00
  · exact block_05_01
  · exact block_05_02
  · exact block_05_03
  · exact block_05_04
  · exact block_05_05
  · exact block_05_06
  · exact block_05_07
  · exact block_05_08
  · exact block_05_09
  · exact block_05_10
  · exact block_05_11
  · exact block_05_12
  · exact block_05_13
  · exact block_05_14
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

end SerreMarkov.PositiveBounded
