import SerreMarkov.PositiveThreeFourBase

namespace SerreMarkov.PositiveThreeFour
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked_5_3_0 : blockCheck 5 3 0=true := by decide +kernel
theorem checked_5_3_1 : blockCheck 5 3 1=true := by decide +kernel
theorem checked_5_3_2 : blockCheck 5 3 2=true := by decide +kernel
theorem checked_5_3_3 : blockCheck 5 3 3=true := by decide +kernel
theorem checked_5_3_4 : blockCheck 5 3 4=true := by decide +kernel
theorem checked_5_3_5 : blockCheck 5 3 5=true := by decide +kernel
theorem checked_5_3_6 : blockCheck 5 3 6=true := by decide +kernel
theorem checked_5_3_7 : blockCheck 5 3 7=true := by decide +kernel
theorem checked_5_3_8 : blockCheck 5 3 8=true := by decide +kernel
theorem checked_5_3_9 : blockCheck 5 3 9=true := by decide +kernel
theorem checked_5_3_10 : blockCheck 5 3 10=true := by decide +kernel
end SerreMarkov.PositiveThreeFour
