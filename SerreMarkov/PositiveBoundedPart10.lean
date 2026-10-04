import SerreMarkov.PositiveBoundedPart09

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_10_00 : blockCheck 10 0 = true := by decide +kernel

theorem block_10_01 : blockCheck 10 1 = true := by decide +kernel

theorem block_10_02 : blockCheck 10 2 = true := by decide +kernel

theorem block_10_03 : blockCheck 10 3 = true := by decide +kernel

theorem block_10_04 : blockCheck 10 4 = true := by decide +kernel

theorem block_10_05 : blockCheck 10 5 = true := by decide +kernel

theorem block_10_06 : blockCheck 10 6 = true := by decide +kernel

theorem block_10_07 : blockCheck 10 7 = true := by decide +kernel

theorem block_10_08 : blockCheck 10 8 = true := by decide +kernel

theorem block_10_09 : blockCheck 10 9 = true := by decide +kernel

theorem checked_row_10 (b : Fin 20) (h : 10+b.val ≤ 19) :
    blockCheck 10 b.val = true := by
  fin_cases b
  · exact block_10_00
  · exact block_10_01
  · exact block_10_02
  · exact block_10_03
  · exact block_10_04
  · exact block_10_05
  · exact block_10_06
  · exact block_10_07
  · exact block_10_08
  · exact block_10_09
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
