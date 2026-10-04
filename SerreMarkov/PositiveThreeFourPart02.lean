import SerreMarkov.PositiveThreeFourBase

namespace SerreMarkov.PositiveThreeFour
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked_4_2_0 : blockCheck 4 2 0=true := by decide +kernel
theorem checked_4_2_1 : blockCheck 4 2 1=true := by decide +kernel
theorem checked_4_2_2 : blockCheck 4 2 2=true := by decide +kernel
theorem checked_4_2_3 : blockCheck 4 2 3=true := by decide +kernel
theorem checked_4_2_4 : blockCheck 4 2 4=true := by decide +kernel
theorem checked_4_2_5 : blockCheck 4 2 5=true := by decide +kernel
theorem checked_4_2_6 : blockCheck 4 2 6=true := by decide +kernel
theorem checked_4_2_7 : blockCheck 4 2 7=true := by decide +kernel
theorem checked_4_2_8 : blockCheck 4 2 8=true := by decide +kernel
theorem checked_4_2_9 : blockCheck 4 2 9=true := by decide +kernel
theorem checked_4_2_10 : blockCheck 4 2 10=true := by decide +kernel
end SerreMarkov.PositiveThreeFour
