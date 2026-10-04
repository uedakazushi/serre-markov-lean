import SerreMarkov.PositiveThreeFourBase

namespace SerreMarkov.PositiveThreeFour
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked_7_1_0 : blockCheck 7 1 0=true := by decide +kernel
theorem checked_7_1_1 : blockCheck 7 1 1=true := by decide +kernel
theorem checked_7_1_2 : blockCheck 7 1 2=true := by decide +kernel
theorem checked_7_1_3 : blockCheck 7 1 3=true := by decide +kernel
theorem checked_7_1_4 : blockCheck 7 1 4=true := by decide +kernel
theorem checked_7_1_5 : blockCheck 7 1 5=true := by decide +kernel
theorem checked_7_1_6 : blockCheck 7 1 6=true := by decide +kernel
theorem checked_7_1_7 : blockCheck 7 1 7=true := by decide +kernel
theorem checked_7_1_8 : blockCheck 7 1 8=true := by decide +kernel
theorem checked_7_1_9 : blockCheck 7 1 9=true := by decide +kernel
theorem checked_7_1_10 : blockCheck 7 1 10=true := by decide +kernel
end SerreMarkov.PositiveThreeFour
