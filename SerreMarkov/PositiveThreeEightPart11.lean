import SerreMarkov.PositiveThreeEightBase
namespace SerreMarkov.PositiveThreeEight
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_15_0 : blockCheck 15 0=true := by decide +kernel
theorem checked_15_1 : blockCheck 15 1=true := by decide +kernel
theorem checked_15_2 : blockCheck 15 2=true := by decide +kernel
theorem checked_15_3 : blockCheck 15 3=true := by decide +kernel
theorem checked_15_4 : blockCheck 15 4=true := by decide +kernel
theorem checked_15_5 : blockCheck 15 5=true := by decide +kernel
theorem checked_15_6 : blockCheck 15 6=true := by decide +kernel
theorem checked_15_7 : blockCheck 15 7=true := by decide +kernel
end SerreMarkov.PositiveThreeEight
