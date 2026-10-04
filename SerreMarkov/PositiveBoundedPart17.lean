import SerreMarkov.PositiveBoundedPart16

namespace SerreMarkov.PositiveBounded

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option linter.unusedVariables false

theorem block_17_00 : blockCheck 17 0 = true := by decide +kernel

theorem block_17_01 : blockCheck 17 1 = true := by decide +kernel

theorem block_17_02 : blockCheck 17 2 = true := by decide +kernel

theorem checked_row_17 (b : Fin 20) (h : 17+b.val ≤ 19) :
    blockCheck 17 b.val = true := by
  fin_cases b
  · exact block_17_00
  · exact block_17_01
  · exact block_17_02
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
