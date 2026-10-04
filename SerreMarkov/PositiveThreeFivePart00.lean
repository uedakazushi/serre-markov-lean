import SerreMarkov.PositiveThreeFiveBase
namespace SerreMarkov.PositiveThreeFive
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_4_0 : blockCheck 4 0=true := by decide +kernel
theorem checked_4_1 : blockCheck 4 1=true := by decide +kernel
theorem checked_4_2 : blockCheck 4 2=true := by decide +kernel
theorem checked_4_3 : blockCheck 4 3=true := by decide +kernel
theorem checked_4_4 : blockCheck 4 4=true := by decide +kernel
theorem checked_4_5 : blockCheck 4 5=true := by decide +kernel
theorem checked_4_6 : blockCheck 4 6=true := by decide +kernel
theorem checked_4_7 : blockCheck 4 7=true := by decide +kernel
theorem checked_4_8 : blockCheck 4 8=true := by decide +kernel
theorem checked_4_9 : blockCheck 4 9=true := by decide +kernel
theorem checked_4_10 : blockCheck 4 10=true := by decide +kernel
end SerreMarkov.PositiveThreeFive
