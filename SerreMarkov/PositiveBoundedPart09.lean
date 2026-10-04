import SerreMarkov.PositiveBoundedPart08

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_09_00 : blockCheck 9 0 = true := by decide +kernel

theorem block_09_01 : blockCheck 9 1 = true := by decide +kernel

theorem block_09_02 : blockCheck 9 2 = true := by decide +kernel

theorem block_09_03 : blockCheck 9 3 = true := by decide +kernel

theorem block_09_04 : blockCheck 9 4 = true := by decide +kernel

theorem block_09_05 : blockCheck 9 5 = true := by decide +kernel

theorem block_09_06 : blockCheck 9 6 = true := by decide +kernel

theorem block_09_07 : blockCheck 9 7 = true := by decide +kernel

theorem block_09_08 : blockCheck 9 8 = true := by decide +kernel

theorem block_09_09 : blockCheck 9 9 = true := by decide +kernel

theorem block_09_10 : blockCheck 9 10 = true := by decide +kernel

theorem checked_row_09 (b : Fin 20) (h : 9+b.val ≤ 19) :
    blockCheck 9 b.val = true := by
  fin_cases b
  · exact block_09_00
  · exact block_09_01
  · exact block_09_02
  · exact block_09_03
  · exact block_09_04
  · exact block_09_05
  · exact block_09_06
  · exact block_09_07
  · exact block_09_08
  · exact block_09_09
  · exact block_09_10
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
