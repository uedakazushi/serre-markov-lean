import SerreMarkov.PositiveBoundedPart00

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_01_00 : blockCheck 1 0 = true := by decide +kernel

theorem block_01_01 : blockCheck 1 1 = true := by decide +kernel

theorem block_01_02 : blockCheck 1 2 = true := by decide +kernel

theorem block_01_03 : blockCheck 1 3 = true := by decide +kernel

theorem block_01_04 : blockCheck 1 4 = true := by decide +kernel

theorem block_01_05 : blockCheck 1 5 = true := by decide +kernel

theorem block_01_06 : blockCheck 1 6 = true := by decide +kernel

theorem block_01_07 : blockCheck 1 7 = true := by decide +kernel

theorem block_01_08 : blockCheck 1 8 = true := by decide +kernel

theorem block_01_09 : blockCheck 1 9 = true := by decide +kernel

theorem block_01_10 : blockCheck 1 10 = true := by decide +kernel

theorem block_01_11 : blockCheck 1 11 = true := by decide +kernel

theorem block_01_12 : blockCheck 1 12 = true := by decide +kernel

theorem block_01_13 : blockCheck 1 13 = true := by decide +kernel

theorem block_01_14 : blockCheck 1 14 = true := by decide +kernel

theorem block_01_15 : blockCheck 1 15 = true := by decide +kernel

theorem block_01_16 : blockCheck 1 16 = true := by decide +kernel

theorem block_01_17 : blockCheck 1 17 = true := by decide +kernel

theorem block_01_18 : blockCheck 1 18 = true := by decide +kernel

theorem checked_row_01 (b : Fin 20) (h : 1+b.val ≤ 19) :
    blockCheck 1 b.val = true := by
  fin_cases b
  · exact block_01_00
  · exact block_01_01
  · exact block_01_02
  · exact block_01_03
  · exact block_01_04
  · exact block_01_05
  · exact block_01_06
  · exact block_01_07
  · exact block_01_08
  · exact block_01_09
  · exact block_01_10
  · exact block_01_11
  · exact block_01_12
  · exact block_01_13
  · exact block_01_14
  · exact block_01_15
  · exact block_01_16
  · exact block_01_17
  · exact block_01_18
  · norm_num at h

end SerreMarkov.PositiveBounded
