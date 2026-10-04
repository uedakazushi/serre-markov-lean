import SerreMarkov.PositiveBoundedPart17

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_18_00 : blockCheck 18 0 = true := by decide +kernel

theorem block_18_01 : blockCheck 18 1 = true := by decide +kernel

theorem checked_row_18 (b : Fin 20) (h : 18+b.val ≤ 19) :
    blockCheck 18 b.val = true := by
  fin_cases b
  · exact block_18_00
  · exact block_18_01
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
  · norm_num at h
  · norm_num at h

end SerreMarkov.PositiveBounded
