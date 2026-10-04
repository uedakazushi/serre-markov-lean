import SerreMarkov.PositiveThreeFourBase

namespace SerreMarkov.PositiveThreeFour
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked_4_1_0 : blockCheck 4 1 0=true := by decide +kernel
theorem checked_4_1_1 : blockCheck 4 1 1=true := by decide +kernel
theorem checked_4_1_2 : blockCheck 4 1 2=true := by decide +kernel
theorem checked_4_1_3 : blockCheck 4 1 3=true := by decide +kernel
theorem checked_4_1_4 : blockCheck 4 1 4=true := by decide +kernel
theorem checked_4_1_5 : blockCheck 4 1 5=true := by decide +kernel
theorem checked_4_1_6 : blockCheck 4 1 6=true := by decide +kernel
theorem checked_4_1_7 : blockCheck 4 1 7=true := by decide +kernel
theorem checked_4_1_8 : blockCheck 4 1 8=true := by decide +kernel
theorem checked_4_1_9 : blockCheck 4 1 9=true := by decide +kernel
theorem checked_4_1_10 : blockCheck 4 1 10=true := by decide +kernel
end SerreMarkov.PositiveThreeFour
