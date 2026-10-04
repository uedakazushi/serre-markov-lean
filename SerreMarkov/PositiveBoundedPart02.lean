import SerreMarkov.PositiveBoundedPart01

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_02_00 : blockCheck 2 0 = true := by decide +kernel

theorem block_02_01 : blockCheck 2 1 = true := by decide +kernel

theorem block_02_02 : blockCheck 2 2 = true := by decide +kernel

theorem block_02_03 : blockCheck 2 3 = true := by decide +kernel

theorem block_02_04 : blockCheck 2 4 = true := by decide +kernel

theorem block_02_05 : blockCheck 2 5 = true := by decide +kernel

theorem block_02_06 : blockCheck 2 6 = true := by decide +kernel

theorem block_02_07 : blockCheck 2 7 = true := by decide +kernel

theorem block_02_08 : blockCheck 2 8 = true := by decide +kernel

theorem block_02_09 : blockCheck 2 9 = true := by decide +kernel

theorem block_02_10 : blockCheck 2 10 = true := by decide +kernel

theorem block_02_11 : blockCheck 2 11 = true := by decide +kernel

theorem block_02_12 : blockCheck 2 12 = true := by decide +kernel

theorem block_02_13 : blockCheck 2 13 = true := by decide +kernel

theorem block_02_14 : blockCheck 2 14 = true := by decide +kernel

theorem block_02_15 : blockCheck 2 15 = true := by decide +kernel

theorem block_02_16 : blockCheck 2 16 = true := by decide +kernel

theorem block_02_17 : blockCheck 2 17 = true := by decide +kernel

theorem checked_row_02 (b : Fin 20) (h : 2+b.val ≤ 19) :
    blockCheck 2 b.val = true := by
  fin_cases b
  · exact block_02_00
  · exact block_02_01
  · exact block_02_02
  · exact block_02_03
  · exact block_02_04
  · exact block_02_05
  · exact block_02_06
  · exact block_02_07
  · exact block_02_08
  · exact block_02_09
  · exact block_02_10
  · exact block_02_11
  · exact block_02_12
  · exact block_02_13
  · exact block_02_14
  · exact block_02_15
  · exact block_02_16
  · exact block_02_17
  · norm_num at h
  · norm_num at h

end SerreMarkov.PositiveBounded
