import SerreMarkov.PositiveBoundedPart05

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_06_00 : blockCheck 6 0 = true := by decide +kernel

theorem block_06_01 : blockCheck 6 1 = true := by decide +kernel

theorem block_06_02 : blockCheck 6 2 = true := by decide +kernel

theorem block_06_03 : blockCheck 6 3 = true := by decide +kernel

theorem block_06_04 : blockCheck 6 4 = true := by decide +kernel

theorem block_06_05 : blockCheck 6 5 = true := by decide +kernel

theorem block_06_06 : blockCheck 6 6 = true := by decide +kernel

theorem block_06_07 : blockCheck 6 7 = true := by decide +kernel

theorem block_06_08 : blockCheck 6 8 = true := by decide +kernel

theorem block_06_09 : blockCheck 6 9 = true := by decide +kernel

theorem block_06_10 : blockCheck 6 10 = true := by decide +kernel

theorem block_06_11 : blockCheck 6 11 = true := by decide +kernel

theorem block_06_12 : blockCheck 6 12 = true := by decide +kernel

theorem block_06_13 : blockCheck 6 13 = true := by decide +kernel

theorem checked_row_06 (b : Fin 20) (h : 6+b.val ≤ 19) :
    blockCheck 6 b.val = true := by
  fin_cases b
  · exact block_06_00
  · exact block_06_01
  · exact block_06_02
  · exact block_06_03
  · exact block_06_04
  · exact block_06_05
  · exact block_06_06
  · exact block_06_07
  · exact block_06_08
  · exact block_06_09
  · exact block_06_10
  · exact block_06_11
  · exact block_06_12
  · exact block_06_13
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

end SerreMarkov.PositiveBounded
