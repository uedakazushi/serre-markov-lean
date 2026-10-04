import SerreMarkov.PositiveThreeFourBase

namespace SerreMarkov.PositiveThreeFour
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked_7_2_0 : blockCheck 7 2 0=true := by decide +kernel
theorem checked_7_2_1 : blockCheck 7 2 1=true := by decide +kernel
theorem checked_7_2_2 : blockCheck 7 2 2=true := by decide +kernel
theorem checked_7_2_3 : blockCheck 7 2 3=true := by decide +kernel
theorem checked_7_2_4 : blockCheck 7 2 4=true := by decide +kernel
theorem checked_7_2_5 : blockCheck 7 2 5=true := by decide +kernel
theorem checked_7_2_6 : blockCheck 7 2 6=true := by decide +kernel
theorem checked_7_2_7 : blockCheck 7 2 7=true := by decide +kernel
theorem checked_7_2_8 : blockCheck 7 2 8=true := by decide +kernel
theorem checked_7_2_9 : blockCheck 7 2 9=true := by decide +kernel
theorem checked_7_2_10 : blockCheck 7 2 10=true := by decide +kernel
end SerreMarkov.PositiveThreeFour
