import SerreMarkov.PositiveBoundedBase

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_00_00 : blockCheck 0 0 = true := by decide +kernel

theorem block_00_01 : blockCheck 0 1 = true := by decide +kernel

theorem block_00_02 : blockCheck 0 2 = true := by decide +kernel

theorem block_00_03 : blockCheck 0 3 = true := by decide +kernel

theorem block_00_04 : blockCheck 0 4 = true := by decide +kernel

theorem block_00_05 : blockCheck 0 5 = true := by decide +kernel

theorem block_00_06 : blockCheck 0 6 = true := by decide +kernel

theorem block_00_07 : blockCheck 0 7 = true := by decide +kernel

theorem block_00_08 : blockCheck 0 8 = true := by decide +kernel

theorem block_00_09 : blockCheck 0 9 = true := by decide +kernel

theorem block_00_10 : blockCheck 0 10 = true := by decide +kernel

theorem block_00_11 : blockCheck 0 11 = true := by decide +kernel

theorem block_00_12 : blockCheck 0 12 = true := by decide +kernel

theorem block_00_13 : blockCheck 0 13 = true := by decide +kernel

theorem block_00_14 : blockCheck 0 14 = true := by decide +kernel

theorem block_00_15 : blockCheck 0 15 = true := by decide +kernel

theorem block_00_16 : blockCheck 0 16 = true := by decide +kernel

theorem block_00_17 : blockCheck 0 17 = true := by decide +kernel

theorem block_00_18 : blockCheck 0 18 = true := by decide +kernel

theorem block_00_19 : blockCheck 0 19 = true := by decide +kernel

theorem checked_row_00 (b : Fin 20) (h : 0+b.val ≤ 19) :
    blockCheck 0 b.val = true := by
  fin_cases b
  · exact block_00_00
  · exact block_00_01
  · exact block_00_02
  · exact block_00_03
  · exact block_00_04
  · exact block_00_05
  · exact block_00_06
  · exact block_00_07
  · exact block_00_08
  · exact block_00_09
  · exact block_00_10
  · exact block_00_11
  · exact block_00_12
  · exact block_00_13
  · exact block_00_14
  · exact block_00_15
  · exact block_00_16
  · exact block_00_17
  · exact block_00_18
  · exact block_00_19

end SerreMarkov.PositiveBounded
