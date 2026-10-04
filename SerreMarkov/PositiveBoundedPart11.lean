import SerreMarkov.PositiveBoundedPart10

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_11_00 : blockCheck 11 0 = true := by decide +kernel

theorem block_11_01 : blockCheck 11 1 = true := by decide +kernel

theorem block_11_02 : blockCheck 11 2 = true := by decide +kernel

theorem block_11_03 : blockCheck 11 3 = true := by decide +kernel

theorem block_11_04 : blockCheck 11 4 = true := by decide +kernel

theorem block_11_05 : blockCheck 11 5 = true := by decide +kernel

theorem block_11_06 : blockCheck 11 6 = true := by decide +kernel

theorem block_11_07 : blockCheck 11 7 = true := by decide +kernel

theorem block_11_08 : blockCheck 11 8 = true := by decide +kernel

theorem checked_row_11 (b : Fin 20) (h : 11+b.val ≤ 19) :
    blockCheck 11 b.val = true := by
  fin_cases b
  · exact block_11_00
  · exact block_11_01
  · exact block_11_02
  · exact block_11_03
  · exact block_11_04
  · exact block_11_05
  · exact block_11_06
  · exact block_11_07
  · exact block_11_08
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
  · norm_num at h

end SerreMarkov.PositiveBounded
