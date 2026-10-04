import SerreMarkov.PositiveBoundedPart03

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_04_00 : blockCheck 4 0 = true := by decide +kernel

theorem block_04_01 : blockCheck 4 1 = true := by decide +kernel

theorem block_04_02 : blockCheck 4 2 = true := by decide +kernel

theorem block_04_03 : blockCheck 4 3 = true := by decide +kernel

theorem block_04_04 : blockCheck 4 4 = true := by decide +kernel

theorem block_04_05 : blockCheck 4 5 = true := by decide +kernel

theorem block_04_06 : blockCheck 4 6 = true := by decide +kernel

theorem block_04_07 : blockCheck 4 7 = true := by decide +kernel

theorem block_04_08 : blockCheck 4 8 = true := by decide +kernel

theorem block_04_09 : blockCheck 4 9 = true := by decide +kernel

theorem block_04_10 : blockCheck 4 10 = true := by decide +kernel

theorem block_04_11 : blockCheck 4 11 = true := by decide +kernel

theorem block_04_12 : blockCheck 4 12 = true := by decide +kernel

theorem block_04_13 : blockCheck 4 13 = true := by decide +kernel

theorem block_04_14 : blockCheck 4 14 = true := by decide +kernel

theorem block_04_15 : blockCheck 4 15 = true := by decide +kernel

theorem checked_row_04 (b : Fin 20) (h : 4+b.val ≤ 19) :
    blockCheck 4 b.val = true := by
  fin_cases b
  · exact block_04_00
  · exact block_04_01
  · exact block_04_02
  · exact block_04_03
  · exact block_04_04
  · exact block_04_05
  · exact block_04_06
  · exact block_04_07
  · exact block_04_08
  · exact block_04_09
  · exact block_04_10
  · exact block_04_11
  · exact block_04_12
  · exact block_04_13
  · exact block_04_14
  · exact block_04_15
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

end SerreMarkov.PositiveBounded
