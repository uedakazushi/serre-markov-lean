import SerreMarkov.PositiveThreeEightBase
namespace SerreMarkov.PositiveThreeEight
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_20_0 : blockCheck 20 0=true := by decide +kernel
theorem checked_20_1 : blockCheck 20 1=true := by decide +kernel
theorem checked_20_2 : blockCheck 20 2=true := by decide +kernel
theorem checked_20_3 : blockCheck 20 3=true := by decide +kernel
theorem checked_20_4 : blockCheck 20 4=true := by decide +kernel
end SerreMarkov.PositiveThreeEight
