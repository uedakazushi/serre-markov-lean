import SerreMarkov.PositiveThreeEightBase
namespace SerreMarkov.PositiveThreeEight
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_18_0 : blockCheck 18 0=true := by decide +kernel
theorem checked_18_1 : blockCheck 18 1=true := by decide +kernel
theorem checked_18_2 : blockCheck 18 2=true := by decide +kernel
theorem checked_18_3 : blockCheck 18 3=true := by decide +kernel
theorem checked_18_4 : blockCheck 18 4=true := by decide +kernel
end SerreMarkov.PositiveThreeEight
