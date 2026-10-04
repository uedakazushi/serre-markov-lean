import SerreMarkov.PositiveBoundedPart02

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_03_00 : blockCheck 3 0 = true := by decide +kernel

theorem block_03_01 : blockCheck 3 1 = true := by decide +kernel

theorem block_03_02 : blockCheck 3 2 = true := by decide +kernel

theorem block_03_03 : blockCheck 3 3 = true := by decide +kernel

theorem block_03_04 : blockCheck 3 4 = true := by decide +kernel

theorem block_03_05 : blockCheck 3 5 = true := by decide +kernel

theorem block_03_06 : blockCheck 3 6 = true := by decide +kernel

theorem block_03_07 : blockCheck 3 7 = true := by decide +kernel

theorem block_03_08 : blockCheck 3 8 = true := by decide +kernel

theorem block_03_09 : blockCheck 3 9 = true := by decide +kernel

theorem block_03_10 : blockCheck 3 10 = true := by decide +kernel

theorem block_03_11 : blockCheck 3 11 = true := by decide +kernel

theorem block_03_12 : blockCheck 3 12 = true := by decide +kernel

theorem block_03_13 : blockCheck 3 13 = true := by decide +kernel

theorem block_03_14 : blockCheck 3 14 = true := by decide +kernel

theorem block_03_15 : blockCheck 3 15 = true := by decide +kernel

theorem block_03_16 : blockCheck 3 16 = true := by decide +kernel

theorem checked_row_03 (b : Fin 20) (h : 3+b.val ≤ 19) :
    blockCheck 3 b.val = true := by
  fin_cases b
  · exact block_03_00
  · exact block_03_01
  · exact block_03_02
  · exact block_03_03
  · exact block_03_04
  · exact block_03_05
  · exact block_03_06
  · exact block_03_07
  · exact block_03_08
  · exact block_03_09
  · exact block_03_10
  · exact block_03_11
  · exact block_03_12
  · exact block_03_13
  · exact block_03_14
  · exact block_03_15
  · exact block_03_16
  · norm_num at h
  · norm_num at h
  · norm_num at h

end SerreMarkov.PositiveBounded
