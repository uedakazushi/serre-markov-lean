import SerreMarkov.PositiveBoundedPart15

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_16_00 : blockCheck 16 0 = true := by decide +kernel

theorem block_16_01 : blockCheck 16 1 = true := by decide +kernel

theorem block_16_02 : blockCheck 16 2 = true := by decide +kernel

theorem block_16_03 : blockCheck 16 3 = true := by decide +kernel

theorem checked_row_16 (b : Fin 20) (h : 16+b.val ≤ 19) :
    blockCheck 16 b.val = true := by
  fin_cases b
  · exact block_16_00
  · exact block_16_01
  · exact block_16_02
  · exact block_16_03
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
  · norm_num at h
  · norm_num at h

end SerreMarkov.PositiveBounded
