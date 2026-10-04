import SerreMarkov.PositiveBoundedPart07

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_08_00 : blockCheck 8 0 = true := by decide +kernel

theorem block_08_01 : blockCheck 8 1 = true := by decide +kernel

theorem block_08_02 : blockCheck 8 2 = true := by decide +kernel

theorem block_08_03 : blockCheck 8 3 = true := by decide +kernel

theorem block_08_04 : blockCheck 8 4 = true := by decide +kernel

theorem block_08_05 : blockCheck 8 5 = true := by decide +kernel

theorem block_08_06 : blockCheck 8 6 = true := by decide +kernel

theorem block_08_07 : blockCheck 8 7 = true := by decide +kernel

theorem block_08_08 : blockCheck 8 8 = true := by decide +kernel

theorem block_08_09 : blockCheck 8 9 = true := by decide +kernel

theorem block_08_10 : blockCheck 8 10 = true := by decide +kernel

theorem block_08_11 : blockCheck 8 11 = true := by decide +kernel

theorem checked_row_08 (b : Fin 20) (h : 8+b.val ≤ 19) :
    blockCheck 8 b.val = true := by
  fin_cases b
  · exact block_08_00
  · exact block_08_01
  · exact block_08_02
  · exact block_08_03
  · exact block_08_04
  · exact block_08_05
  · exact block_08_06
  · exact block_08_07
  · exact block_08_08
  · exact block_08_09
  · exact block_08_10
  · exact block_08_11
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

end SerreMarkov.PositiveBounded
