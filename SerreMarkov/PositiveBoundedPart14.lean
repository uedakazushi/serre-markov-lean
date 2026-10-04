import SerreMarkov.PositiveBoundedPart13

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_14_00 : blockCheck 14 0 = true := by decide +kernel

theorem block_14_01 : blockCheck 14 1 = true := by decide +kernel

theorem block_14_02 : blockCheck 14 2 = true := by decide +kernel

theorem block_14_03 : blockCheck 14 3 = true := by decide +kernel

theorem block_14_04 : blockCheck 14 4 = true := by decide +kernel

theorem block_14_05 : blockCheck 14 5 = true := by decide +kernel

theorem checked_row_14 (b : Fin 20) (h : 14+b.val ≤ 19) :
    blockCheck 14 b.val = true := by
  fin_cases b
  · exact block_14_00
  · exact block_14_01
  · exact block_14_02
  · exact block_14_03
  · exact block_14_04
  · exact block_14_05
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
  · norm_num at h
  · norm_num at h
  · norm_num at h

end SerreMarkov.PositiveBounded
