import SerreMarkov.PositiveThreeEightBase
namespace SerreMarkov.PositiveThreeEight
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_16_0 : blockCheck 16 0=true := by decide +kernel
theorem checked_16_1 : blockCheck 16 1=true := by decide +kernel
theorem checked_16_2 : blockCheck 16 2=true := by decide +kernel
theorem checked_16_3 : blockCheck 16 3=true := by decide +kernel
theorem checked_16_4 : blockCheck 16 4=true := by decide +kernel
theorem checked_16_5 : blockCheck 16 5=true := by decide +kernel
end SerreMarkov.PositiveThreeEight
