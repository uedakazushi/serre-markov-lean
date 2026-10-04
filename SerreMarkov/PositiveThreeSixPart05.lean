import SerreMarkov.PositiveThreeSixBase
namespace SerreMarkov.PositiveThreeSix
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_9_0 : blockCheck 9 0=true := by decide +kernel
theorem checked_9_1 : blockCheck 9 1=true := by decide +kernel
theorem checked_9_2 : blockCheck 9 2=true := by decide +kernel
theorem checked_9_3 : blockCheck 9 3=true := by decide +kernel
theorem checked_9_4 : blockCheck 9 4=true := by decide +kernel
theorem checked_9_5 : blockCheck 9 5=true := by decide +kernel
theorem checked_9_6 : blockCheck 9 6=true := by decide +kernel
end SerreMarkov.PositiveThreeSix
