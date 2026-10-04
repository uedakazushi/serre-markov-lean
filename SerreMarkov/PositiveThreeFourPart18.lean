import SerreMarkov.PositiveThreeFourBase

namespace SerreMarkov.PositiveThreeFour
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked_8_2_0 : blockCheck 8 2 0=true := by decide +kernel
theorem checked_8_2_1 : blockCheck 8 2 1=true := by decide +kernel
theorem checked_8_2_2 : blockCheck 8 2 2=true := by decide +kernel
theorem checked_8_2_3 : blockCheck 8 2 3=true := by decide +kernel
theorem checked_8_2_4 : blockCheck 8 2 4=true := by decide +kernel
theorem checked_8_2_5 : blockCheck 8 2 5=true := by decide +kernel
theorem checked_8_2_6 : blockCheck 8 2 6=true := by decide +kernel
theorem checked_8_2_7 : blockCheck 8 2 7=true := by decide +kernel
theorem checked_8_2_8 : blockCheck 8 2 8=true := by decide +kernel
theorem checked_8_2_9 : blockCheck 8 2 9=true := by decide +kernel
theorem checked_8_2_10 : blockCheck 8 2 10=true := by decide +kernel
end SerreMarkov.PositiveThreeFour
