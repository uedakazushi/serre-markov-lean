import SerreMarkov.PositiveThreeFourBase

namespace SerreMarkov.PositiveThreeFour
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked_4_0_0 : blockCheck 4 0 0=true := by decide +kernel
theorem checked_4_0_1 : blockCheck 4 0 1=true := by decide +kernel
theorem checked_4_0_2 : blockCheck 4 0 2=true := by decide +kernel
theorem checked_4_0_3 : blockCheck 4 0 3=true := by decide +kernel
theorem checked_4_0_4 : blockCheck 4 0 4=true := by decide +kernel
theorem checked_4_0_5 : blockCheck 4 0 5=true := by decide +kernel
theorem checked_4_0_6 : blockCheck 4 0 6=true := by decide +kernel
theorem checked_4_0_7 : blockCheck 4 0 7=true := by decide +kernel
theorem checked_4_0_8 : blockCheck 4 0 8=true := by decide +kernel
theorem checked_4_0_9 : blockCheck 4 0 9=true := by decide +kernel
theorem checked_4_0_10 : blockCheck 4 0 10=true := by decide +kernel
end SerreMarkov.PositiveThreeFour
